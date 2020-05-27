(ns phynaster.logic)

;; Term = LVar | Value | Seq Term
;;
;; u v w : Term
;; p q r : LVar
;; x y z : Value
;;
;; a term is either a logical variable (lvar) or a value.
;; a lvar is implemented as a vector/list whose head is ::lvar,
;; to circumvent the restriction in clojure that sequences must have proper tails,
;; so that a lvar could unify with a tail.
;;
;; id of type Nat is reserved for exist,
;; when constructing lvar manually,
;; one must supply an id of another type.

(defn lvar [id] [::lvar id])
(defn lvar? [u] (and (sequential? u) (= (first u) ::lvar)))
(defn toseq [u] (and (sequential? u) (seq u)))

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

;; Node =
;; | cont : () -> Node
;; | pair : Pair = Unit * Node
;; | unit : Unit = SMap * NVar * CSet
;; | zero = nil
;;
;; a node in the search tree can be
;; - cont, a continuation/thunk which when called may eventually produce a mature node
;; - zero, a mature node reprenseting a failure state
;; - unit, a mature node representing a success state
;; - pair, a mature node containing a state unit and a successor node
;;
;; NVar = Nat
;; CSet = Set Constraint
;; Goal = Unit -> Node
;;
;; bind : Node * Goal -> Node
;; plus : Node * Node -> Node
;; pull : Node -> LazySeq Unit

(defprotocol Node
  (bind [this goal])
  (plus [this that])
  (pull [this]))

(defrecord Pair [unit node]
  Node
  (bind [this goal] (plus (goal unit) (bind node goal)))
  (plus [this that] (Pair. unit (plus node that)))
  (pull [this] (lazy-seq (cons unit (lazy-seq (pull node))))))

(defrecord Unit [smap nvar cset]
  Node
  (bind [this goal] (goal this))
  (plus [this that] (Pair. this that))
  (pull [this] (list this)))
(def alpha (Unit. {} 0 #{}))

(def zero nil)
(extend-protocol Node
  nil
  (bind [this goal] zero)
  (plus [this that] that)
  (pull [this] ()))

(extend-protocol Node
  clojure.lang.Fn
  (bind [this goal] #(bind (this) goal))
  (plus [this that] #(plus that (this)))
  (pull [this] (pull (trampoline this))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; goals and constraints ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; === : Term * Term -> Goal
;;
;; capply : Constraint * Unit -> Maybe Unit
;; creify : Constraint * SMap -> SMap ???? TODO
;; ccheck : Unit -> Maybe Unit

(defprotocol Constraint
  (capply [this unit]))

(defn ccheck [{:keys [cset] :as unit}]
  (reduce (fn [?unit constraint]
            (if-let [unit ?unit]
              (capply constraint unit)
              (reduced nil)))
          unit cset))

(defn === [u v]
  (fn [{:keys [smap] :as unit}]
    (when-let [smap (unify u v smap)]
      (ccheck (assoc unit :smap smap)))))

(defrecord C=!= [u v]
  ;; TODO commutative, u v order does not matter, can also be extend to multivariate
  Constraint
  (capply [this {:keys [smap] :as unit}]
    (let [?smap (unify u v smap)]
      (cond
        ;; unification fails, already disequal, throw constraint away
        (nil? ?smap)      (update unit :cset disj this)
        ;; unification succeeds by extending smap, keep for future
        (not= ?smap smap) (update unit :cset conj this)
        ;; unification succeeds without extending smap, fail
        :else zero))))

(defn =!= [u v]
  (fn [unit]
    (-> (C=!=. u v)
        (capply unit))))

(defrecord C=domain [u dom]
  ;; dom : Set Value
  Constraint
  (capply [this {:keys [smap] :as unit}]
    (let [u (walk u smap)]
      (cond
        ;; unbound, keep for future
        (lvar? u)         (update unit :cset conj this)
        ;; satisfied, throw constraint away
        (contains? dom u) (update unit :cset disj this)
        ;; violated, fail
        :else zero))))

(defn =domain [u dom]
  (fn [unit]
    (-> (C=domain. u dom)
        (capply unit))))

(defrecord C=unique [qs]
  Constraint
  (capply [this {:keys [smap] :as unit}]
    (let [us (map #(walk % smap) qs)]
      (cond
        ;; violated, fail
        (not (apply distinct? us))              zero
        ;; unbound, keep for future
        (some lvar? us) (update unit :cset conj this)
        ;; satisfied, throw constraint away
        :else           (update unit :cset disj this)))))

(defn =unique [& qs]
  (fn [unit]
    (-> (C=unique. (vec qs))
        (capply unit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; conjunction and disjunction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn g1 [unit] unit)
(defn g0 [unit] zero)

(defn &
  ([] g1)
  ([& gs] (fn [unit] (reduce bind unit gs))))

(defn |
  ([] g0)
  ([g] g)
  ([g g'] (fn [unit] (plus (g unit) #(g' unit))))
  ([g g' & gs] (reduce | g (cons g' gs))))

(defn all [gs] (apply & gs))
(defn any [gs] (apply | gs))

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defn call-exist [lvar->goal]
  (fn [{:keys [nvar] :as unit}]
    ((lvar->goal (lvar nvar))
     (assoc unit :nvar (inc nvar)))))

(defmacro exist
  {:style/indent 1}
  [vars & goals]
  (if (empty? vars)
    `(& ~@goals)
    `(call-exist
      (fn [~(first vars)]
        (exist [~@(rest vars)]
          ~@goals)))))

(defn call-goal [goal]
  (goal alpha))

(defmacro run' [vars & goals]
  `(->> (exist [~@vars] ~@goals)
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

(def ^:macro % #'exist)
(def ^:macro ? #'run*)

;;;;;;;;;;;;;;;;;;;;
;; goal utilities ;;
;;;;;;;;;;;;;;;;;;;;

(defn =cons [a d ls]
  (=== (cons a d) ls))

(defn =append [ls rs lsrs]
  (| (& (=== () ls)
        (=== rs lsrs))
     (% [l s srs]
        (=cons l s ls)
        (=cons l srs lsrs)
        (=append s rs srs))))

(defn =insert [y xs xys]
  (% [lhs rhs]
     (=append lhs rhs xs)
     (=append lhs (cons y rhs) xys)))

(defn =rember [x ls out]
  (| (& (=== () ls)
        (=== () out))
     (% [a d]
        (=cons a d ls)
        (=== a x)
        (=== d out))
     (% [a d res]
        (=cons a d ls)
        (=!= a x)
        (=cons a res out)
        (=rember x d res))))

;; TODO
;; - finite domain constraints
;; - transparent representation
;; - make operators operads
;; - reify constraints

(comment

  (def hints
    [2 0 7 0 1 0 5 0 8
     0 0 0 6 7 8 0 0 0
     8 0 0 0 0 0 0 0 6
     0 7 0 9 0 6 0 5 0
     4 9 0 0 0 0 0 1 3
     0 3 0 4 0 1 0 2 0
     5 0 0 0 0 0 0 0 1
     0 0 0 2 9 4 0 0 0
     3 0 6 0 8 0 4 0 9])

  (defn make-cells [hints]
    (map (fn [cell hint]
           (if (zero? hint)
             (lvar cell)
             hint))
         (for [r (range 9)
               c (range 9)]
           [r c])
         hints))

  (defn make-nines [cells]
    (let [rows (partition 9 cells)
          cols (apply map list rows)
          subs (for [r3c9 (partition 3 rows)
                     r3c3 (partition 3 (apply map list r3c9))]
                 (apply concat r3c3))]
      (concat rows cols subs)))

  (defn sudoku [hints]
    (let [cells (make-cells hints)
          nines (make-nines cells)]
      (->> (run* [q]
             (all (map (partial apply =unique) nines))
             (all (keep (fn [cell]
                          (when (lvar? cell)
                            (any (map (partial === cell)
                                      (range 1 10)))))
                        cells))
             (=== q cells))
           (map :q))))

  (defn to-grid [cells]
    (mapv vec (partition 9 cells)))

  (-> hints sudoku first to-grid)

  (doseq [res (sudoku hints)]
    (clojure.pprint/pprint
     (to-grid res)))

  )
