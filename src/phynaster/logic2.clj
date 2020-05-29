(ns phynaster.logic2)

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

(defn lvar [id] [:lvar id])
(defn lvar? [u] (and (sequential? u) (= (first u) :lvar)))
(defn toseq [u] (and (sequential? u) (seq u)))

;;;;;;;;;;;;;;;;;;;;;;;
;; unification rules ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; SMap = Map LVar Term
;; walk : Term , SMap -> Term
;; unify : Term , Term , SMap -> Maybe SMap
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
;; | fork : Fork = Unit+ , Node+
;; | unit : Unit
;;
;; a node in the search tree can be
;; - cont, a continuation/thunk which when run may eventually produce a mature node
;; - fork, a mature node containing a state unit and more successor nodes
;; - unit, a mature node representing a success or failure state
;;
;; Goal = Desc , Call
;; Call = Unit -> Node
;; exec : Unit , Goal -> Unit
;;
;; bind : Node , Goal+ -> Node
;; plus : Node , Node+ -> Node
;; pull : Node -> LazySeq Unit

(defprotocol IBind1 (bind1 [this goal]))

(defprotocol IBind (bind [this goal+]))
(defprotocol IPlus (plus [this that+]))
(defprotocol IExec (exec [this]))
(defprotocol IPull (pull [this]))

;; bind : Thunk , Goal+ -> Thunk
;; bind : State , Goal+ -> Board
;; bind : Board , Goal+ -> Board
;;
;; plus : Thunk , ????+ -> Thunk
;; plus : State , ????+ -> Board
;; plus : Board , Board+ -> Board
;;
;; exec : Board -> Board
;; exec : Thunk -> Thunk | Board
;;
;;

(defn -bind [goal+] (fn [this] (bind this goal+)))

(defrecord Board [thunks states graves]
  IBind
  (bind [this goal+]
    (plus (assoc this
                 :thunks (mapv (-bind goal+) thunks)
                 :states [])
          (map (-bind goal+) states)))
  (IPlus [this that+]
    (Board. (into thunks (mapcat :thunks that+))
            (into states (mapcat :states that+))
            (into graves (mapcat :graves that+))))
  IExec
  (exec [this]
    (let [[thunk & thunks] thunks
          this (assoc this :thunks (vec thunks))
          that (exec thunk)]
      (if (fn? that)
        (update this :thunks conj that)
        (plus this [that]))))
  IPull
  (pull [this]



    (concat units (lazy-seq (mapcat pull thunks))))



  )

(extend-type clojure.lang.Fn
  IBind
  (bind [this goal+] #(bind (this) goal+))
  IPlus
  (plus [this that+] #(plus (this) that+))
  IExec
  (exec [this] (this))
  IPull
  (pull [this] (pull (trampoline this))))

(defrecord State [alive smap cg dg]
  IBind1
  (bind1 [this {:as goal :keys [desc call]}]
    (if alive
      (let [this (assoc this
                        :dg (conj dg cg)
                        :cg desc)]
        (if-let [this (call this)]
          this
          (assoc this :alive false)))
      this))
  IBind
  (bind [this goal+] (reduce bind1 this goal+))
  IPlus
  (plus [this that+]
    ;; TODO
    (plus (Fork. [unit] []) that+)
    )
  )

(def initial-state (State. true {} :init []))
(def initial-board (Board. [] [initial-state] []))

(defrecord Goal [desc call])

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; goals and constraints ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; === : Term , Term -> Goal

(defn === [u v]
  (Goal.
   (list '=== u v)
   (fn [{:keys [smap] :as unit}]
     (when-let [smap (unify u v smap)]
       (assoc unit :smap smap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; conjunction and disjunction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def g1 (Goal. :t (fn [unit] unit)))
(def g0 (Goal. :f (fn [unit] (assoc unit :alive false))))

(defn &
  ([] g1)
  ([& gs]
   (Goal.
    (cons '& (map :desc gs))
    (fn [unit]
      (bind unit gs)))))

(defn |
  ([] g0)
  ([g] g)
  ([g & gs]
   (Goal.
    (cons '| (map :desc (cons g gs)))
    (fn [unit]
      ;; magic happens here
      (plus (exec unit g)
            (map (partial exec unit)
                 gs))))))

(defn all [gs] (apply & gs))
(defn any [gs] (apply | gs))

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defn run
  ([goal] (run goal alpha))
  ([goal unit] (pull (exec unit goal))))

(comment

  (def p (lvar \p))
  (def q (lvar \q))
  (def r (lvar \r))

  (run (| (& (=== p 0)
             (=== p 1))
          (& (=== p 0)
             (=== q 1))))

  (run (| (=== p 0)
          (=== p 1)
          (=== p 2)))

  (run (& (| (=== p 0)
             (=== p 1)
             (=== p 2))
          (=== p 1)))

  (run (| (=== 0 1)
          (| (| (=== 3 4)
                (=== 5 5))
             (=== 2 3))
          (=== 1 2)))

  (defn foo []
    (->> (| (=== 1 1)
            (=== 2 2)
            (=== 3 3)
            (=== 4 4)
            (=== 5 5)
            (=== 6 6)
            (=== 7 7)
            (=== 8 8)
            (=== 9 9))
         run
         (map :cg)
         (map second)))

  )
