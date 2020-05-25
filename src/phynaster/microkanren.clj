(ns phynaster.microkanren)

;; Term = LVar | Value
;;
;; a term is either a logical variable (lvar) or a value.
;; a lvar is implemented as a vector/list whose head is ::lvar,
;; to circumvent the restriction in clojure that sequences must have proper tails,
;; so that a lvar could unify with a tail.
;;
;; id of type Nat is reserved for fresh,
;; when constructing lvar manually,
;; one must supply an id of another type.

(defn lvar [id] [::lvar id])
(defn lvar? [x] (and (sequential? x) (= (first x) ::lvar)))
(defn toseq [x] (and (sequential? x) (seq x)))

;;;;;;;;;;;;;;;;;;;;;;;
;; unification rules ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; SMap = Map LVar Term
;; walk : Term * SMap -> Term
;; unify : Term * Term * SMap -> Maybe SMap
;;
;; unify returns {}   means success trivially
;; unify returns nil  means failure

(defn walk [u smap]
  (if (and (lvar? u) (contains? smap u))
    (recur (smap u) smap)
    u))

(defn unify [u v smap]
  (let [u (walk u smap)  v (walk v smap)]
    (cond
      ;; already unify, return smap unmodified (capply relies on this behavior)
      (= u v) smap
      ;; extend smap for lvar
      (lvar? u) (assoc smap u v)
      (lvar? v) (assoc smap v u)
      ;; unify sequences recursively
      (and (toseq u) (toseq v))
      (when-let [smap (unify (first u) (first v) smap)]
        (recur (rest u) (rest v) smap)))))

;;;;;;;;;;;;;;;;;;;;;;
;; inference engine ;;
;;;;;;;;;;;;;;;;;;;;;;

;; INode =
;; | cont : () -> INode
;; | node : Node = State * INode
;; | zero = nil
;;
;; an inode in the search tree can be
;; - cont, a continuation/thunk which when called may eventually produce a mature node
;; - node, a mature node containing a state and more possible inodes
;; - zero, a mature node reprenseting no (more) results
;;
;; unit : State -> Node
;; bind : INode *  Goal -> INode
;; plus : INode * INode -> INode
;; pull : INode -> LazySeq State

(def zero nil)
(defrecord Node [state inode])
(defprotocol INode
  (bind [this goal])
  (plus [this that])
  (pull [this]))

(extend-protocol INode
  clojure.lang.IFn
  (bind [this goal] #(bind (this) goal))
  (plus [this that] #(plus that (this)))
  (pull [this] (pull (trampoline this)))
  Node
  (bind [{:keys [state inode]} goal] (plus (goal state) (bind inode goal)))
  (plus [{:keys [state inode]} that] (Node. state (plus inode that)))
  (pull [{:keys [state inode]}] (lazy-seq (cons state (pull inode))))
  nil
  (bind [this goal] zero)
  (plus [this that] that)
  (pull [this] ()))

(defn unit [state]
  (Node. state zero))

(defn make-node [?state]
  (if-let [state ?state]
    (unit state)
    zero))

;;;;;;;;;;;;;;;;;
;; constraints ;;
;;;;;;;;;;;;;;;;;

;; capply : IConstraint * State -> Maybe State
;; creify : IConstraint * SMap -> SMap ???? TODO
;; ccheck : State -> Maybe State

(defprotocol IConstraint
  (capply [this state]))

(defrecord C=!= [u v]
  ;; TODO commutative, u v order does not matter, can also be extend to multivariate
  IConstraint
  (capply [this {:keys [smap] :as state}]
    (let [?smap (unify u v smap)]
      (cond
        ;; unification fails, already disequal, throw constraint away
        (nil? ?smap)      (update state :cset disj this)
        ;; unification succeeds by extending smap, keep for future
        (not= ?smap smap) (update state :cset conj this)
        ;; unification succeeds without extending smap, fail
        ))))

(defn =!= [u v]
  (fn [state]
    (-> (C=!=. u v)
        (capply state)
        make-node)))

(defn ccheck [{:keys [cset] :as state}]
  (reduce (fn [?state constraint]
            (when-let [state ?state]
              (capply constraint state)))
          state cset))

;;;;;;;;;;;;;;;;;;;;;;
;; basic constructs ;;
;;;;;;;;;;;;;;;;;;;;;;

;; State = SMap * NVar * CSet
;; NVar = Nat
;; Cset = Set IConstraint
;;
;; Goal = State -> INode
;;
;; === : Term * Term -> Node
;; disjoin : Goal * Goal -> INode
;; conjoin : Goal * Goal -> INode

(defrecord State [smap nvar cset])
(def initial-state (State. {} 0 #{}))

(defn === [u v]
  (fn [{:keys [smap] :as state}]
    (make-node
     (when-let [smap (unify u v smap)]
       (ccheck (assoc state :smap smap))))))

(defn disjoin [goal goal'] (fn [state] (plus (goal state) (goal' state))))
(defn conjoin [goal goal'] (fn [state] (bind (goal state) goal')))

(defn g1 [state] (unit state))
(defn g0 [state] zero)

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defmacro defer [goal] `(fn [state#] (fn [] (~goal state#))))

(defmacro disj+
  ([goal] `(defer ~goal))
  ([goal & goals] `(disjoin (defer ~goal) (disj+ ~@goals))))

(defmacro conj+
  ([goal] `(defer ~goal))
  ([goal & goals] `(conjoin (defer ~goal) (conj+ ~@goals))))

(defmacro conde [& goals]
  `(disj+ ~@(map (fn [goal] `(conj+ ~@goal))
                 goals)))

(defn call-fresh [lvar->goal]
  (fn [{:keys [nvar] :as state}]
    ((lvar->goal (lvar nvar))
     (assoc state :nvar (inc nvar)))))

(defmacro fresh [vars & goals]
  (if (empty? vars)
    `(conj+ ~@goals)
    `(call-fresh
      (fn [~(first vars)]
        (fresh [~@(rest vars)]
          ~@goals)))))

(defn call-goal [goal]
  (goal initial-state))

(defmacro run' [vars & goals]
  `(->> (fresh [~@vars] ~@goals)
        call-goal
        pull))

(defn query-result [vars {:keys [smap nvar]}]
  (letfn [(unk [n] (symbol (str \? n)))
          (dot [v] (if (symbol? v) `(. ~v) v))
          (walk* [v smap]
            (let [v (walk v smap)]
              (cond (lvar? v) v
                    (toseq v) (cons (walk* (first v) smap) (dot (walk* (rest v) smap)))
                    :else v)))
          (fill* [v smap]
            (let [v (walk v smap)]
              (cond (lvar? v) (assoc smap v (unk (count smap)))
                    (toseq v) (fill* (rest v) (fill* (first v) smap))
                    :else smap)))]
    (as-> (lvar nvar) v
      (walk* v (assoc smap v (->> vars count range (map lvar))))
      (zipmap (map keyword vars)
              (walk* v (fill* v {}))))))

(defmacro run* [vars & goals]
  `(map (partial query-result '~vars)
        (run' ~vars ~@goals)))

(defmacro run [n vars & goals]
  `(take ~n (run* ~vars ~@goals)))

;;;;;;;;;;;;;;;;;;;;
;; goal utilities ;;
;;;;;;;;;;;;;;;;;;;;

(defn appendo [ls rs lsrs]
  (conde
   [(=== () ls) (=== rs lsrs)]
   [(fresh [l s srs]
      (=== (cons l s) ls)
      (=== (cons l srs) lsrs)
      (appendo s rs srs))]))

(defn inserto [y xs xys]
  (fresh [lhs rhs]
    (appendo lhs rhs xs)
    (appendo lhs (cons y rhs) xys)))

(defn rembero [x ls out]
  (conde
   [(=== () ls) (=== () out)]
   [(fresh [a d]
      (=== (cons a d) ls)
      (=== a x)
      (=== d out))]
   [(fresh [a d res]
      (=== (cons a d) ls)
      (=!= a x)
      (=== (cons a res) out)
      (rembero x d res))]))
