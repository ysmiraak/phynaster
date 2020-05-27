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
;; | unit : Unit
;;
;; a node in the search tree can be
;; - cont, a continuation/thunk which when called may eventually produce a mature node
;; - unit, a mature node representing a success or failure state
;; - pair, a mature node containing a state unit and a successor node
;;
;; Goal = Desc * (Unit -> Node)
;;
;; bind : Node * Goal -> Node
;; plus : Node * Node -> Node
;; pull : Node -> LazySeq Unit

(defrecord Goal [desc call])

(defn exec [{:keys [desc call]}
            {:keys [smap cg dg alive] :as unit}]
  (if alive
    (let [unit (assoc unit
                      :dg (conj dg cg)
                      :cg desc)]
      (if-let [unit (call unit)]
        unit
        (assoc unit :alive false)))
    unit))

(defprotocol Node
  (bind [this goal])
  (plus [this that])
  (pull [this]))

(defrecord Pair [unit node]
  Node
  (bind [this goal] (plus (exec goal unit) (bind node goal)))
  (plus [this that] (Pair. unit (plus node that)))
  (pull [this] (lazy-seq (cons unit (lazy-seq (pull node))))))

(defrecord Unit [alive smap cg dg]
  Node
  (bind [this goal] (exec goal this))
  (plus [this that] (Pair. this that))
  (pull [this] (list this)))

(def alpha (Unit. true {} :init []))

;; (def zero nil)
;; (extend-protocol Node
;;   nil
;;   (bind [this goal] zero)
;;   (plus [this that] that)
;;   (pull [this] ()))

(extend-protocol Node
  clojure.lang.Fn
  (bind [this goal] #(bind (this) goal))
  (plus [this that] #(plus that (this)))
  (pull [this] (pull (trampoline this))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; goals and constraints ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; === : Term * Term -> Goal

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
      (reduce bind unit gs)))))

(defn |
  ([] g0)
  ([g] g)
  ([g g']
   (Goal.
    (list '| (:desc g) (:desc g'))
    (fn [unit]
      (plus (exec g unit)
            #(exec g' unit)))))
  ([g g' & gs] (reduce | g (cons g' gs))))

(defn all [gs] (apply & gs))
(defn any [gs] (apply | gs))

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defn exec1
  ([goal] (exec1 goal alpha))
  ([goal unit]
   (let [node (exec goal unit)]
     (if (fn? node)
       (trampoline node)
       node))))

(defn exec* [goal]
  (when-let [node (exec1 goal)]
    (if (instance? Pair node)
      (let [{:keys [node] :as pair} node]
        (if (fn? node)
          (assoc pair :node (trampoline node))
          pair))
      node)))

(comment

  (def p (lvar \p))
  (def q (lvar \q))
  (def r (lvar \r))

  (| (& (=== p 0)
        (=== p 1))
     (& (=== p 0)
        (=== q 1)))
  =>
  {:unit {:alive false,
          :smap {[:lvar \p] 0},
          :cg (=== [:lvar \p] 1),
          :dg [:init
               (| (& (=== [:lvar \p] 0)
                     (=== [:lvar \p] 1))
                  (& (=== [:lvar \p] 0)
                     (=== [:lvar \q] 1)))
               (& (=== [:lvar \p] 0)
                  (=== [:lvar \p] 1))
               (=== [:lvar \p] 0)]},
   :node {:alive true,
          :smap {[:lvar \p] 0, [:lvar \q] 1},
          :cg (=== [:lvar \q] 1),
          :dg [:init
               (| (& (=== [:lvar \p] 0)
                     (=== [:lvar \p] 1))
                  (& (=== [:lvar \p] 0)
                     (=== [:lvar \q] 1)))
               (& (=== [:lvar \p] 0)
                  (=== [:lvar \q] 1))
               (=== [:lvar \p] 0)]}}

  (exec* (| (=== p 0)
            (=== p 1)
            (=== p 2)))
  =>
  {:unit {:alive true,
          :smap {[:lvar \p] 0},
          :cg (=== [:lvar \p] 0),
          :dg [:init
               (| (| (=== [:lvar \p] 0)
                     (=== [:lvar \p] 1))
                  (=== [:lvar \p] 2))
               (| (=== [:lvar \p] 0)
                  (=== [:lvar \p] 1))]},
   :node {:unit {:alive true,
                 :smap {[:lvar \p] 1},
                 :cg (=== [:lvar \p] 1),
                 :dg [:init
                      (| (| (=== [:lvar \p] 0)
                            (=== [:lvar \p] 1))
                         (=== [:lvar \p] 2))
                      (| (=== [:lvar \p] 0)
                         (=== [:lvar \p] 1))]},
          :node {:alive true,
                 :smap {[:lvar \p] 2},
                 :cg (=== [:lvar \p] 2),
                 :dg [:init
                      (| (| (=== [:lvar \p] 0)
                            (=== [:lvar \p] 1))
                         (=== [:lvar \p] 2))]}}}

  (exec* (& (| (=== p 0)
               (=== p 1)
               (=== p 2))
            (=== p 1)))
  =>
  {:unit {:alive false,
          :smap {[:lvar \p] 0},
          :cg (=== [:lvar \p] 1),
          :dg [:init
               (& (| (| (=== [:lvar \p] 0)
                        (=== [:lvar \p] 1))
                     (=== [:lvar \p] 2))
                  (=== [:lvar \p] 1))
               (| (| (=== [:lvar \p] 0)
                     (=== [:lvar \p] 1))
                  (=== [:lvar \p] 2))
               (| (=== [:lvar \p] 0)
                  (=== [:lvar \p] 1))
               (=== [:lvar \p] 0)]},
   :node {:unit {:alive true,
                 :smap {[:lvar \p] 1},
                 :cg (=== [:lvar \p] 1),
                 :dg [:init
                      (& (| (| (=== [:lvar \p] 0)
                               (=== [:lvar \p] 1))
                            (=== [:lvar \p] 2))
                         (=== [:lvar \p] 1))
                      (| (| (=== [:lvar \p] 0)
                            (=== [:lvar \p] 1))
                         (=== [:lvar \p] 2))
                      (| (=== [:lvar \p] 0)
                         (=== [:lvar \p] 1))
                      (=== [:lvar \p] 1)]},
          :node {:alive false,
                 :smap {[:lvar \p] 2},
                 :cg (=== [:lvar \p] 1),
                 :dg [:init
                      (& (| (| (=== [:lvar \p] 0)
                               (=== [:lvar \p] 1))
                            (=== [:lvar \p] 2))
                         (=== [:lvar \p] 1))
                      (| (| (=== [:lvar \p] 0)
                            (=== [:lvar \p] 1))
                         (=== [:lvar \p] 2))
                      (=== [:lvar \p] 2)]}}}

  )
