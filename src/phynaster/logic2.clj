(ns phynaster.logic2)

;; Term = LVar | Value | Seq Term
;;
;; u v w : Term
;; p q r : LVar
;; x y z : Value
;;
;; a term is either a logical variable (lvar) or a value.
;; a lvar is implemented as a vector/list whose head is :lvar,
;; to circumvent the restriction in clojure that sequences must have proper tails,
;; so that a lvar could unify with a tail.

(defn lvar [id] [:lvar id])
(defn lvar? [u] (and (sequential? u) (= (first u) :lvar)))
(defn toseq [u] (and (sequential? u) (seq u)))

(defn queue
  ([] clojure.lang.PersistentQueue/EMPTY)
  ([x] (conj (queue) x))
  ([x & xs] (into (queue x) xs)))
(defn mapq [f xs] (into (queue) (map f xs)))

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

;; Thunk = Goal , State
;; Goal  = Desc , Cont
;; Cont  = State -> Board
;;
;; plus : Board , Board+ -> Board
;; bind : Board , Goal -> Board
;; bind : State , Goal -> Board
;; bind : Thunk , Goal -> Thunk
;; exec : Thunk -> Board
;; exec : Board -> Board

(defprotocol Bind (bind [this goal]))
(defprotocol Plus (plus [this that+]))
(defprotocol Exec (exec [this]))

(defrecord Goal [desc cont])
(defn call [goal] (fn [this] (bind this goal)))

(defrecord Board [state* thunk* grave*]
  Plus (plus [this that+]
         (Board. (into state* (mapcat :state* that+))
                 (into thunk* (mapcat :thunk* that+))
                 (into grave* (mapcat :grave* that+))))
  Bind (bind [this goal]
         (plus (Board. [] (mapq (call goal) thunk*) grave*)
               (map (call goal) state*)))
  Exec (exec [this]
         (if (seq thunk*)
           ;; force thunks in cycle, this is where magic happens
           ;; 0. given a model : Thunk -> Logit
           ;; 1. assign a logit priority to each thunk
           ;; 2. exec thunk with the highest priority
           ;; 3. repeat from 2 til no more thunks
           ;; 4. update model by the alive likelihood
           (plus (update this :thunk* pop)
                 [(exec (peek  thunk*))])
           this)))

(declare &)
(defrecord Thunk [state goal]
  Bind (bind [this goal'] (assoc this :goal (& goal goal')))
  Exec (exec [this] (bind state goal)))
(defrecord State [smap done] Bind (bind [this {:keys [desc cont]}] (cont (update this :done conj desc))))
(defrecord Grave [smap done] Bind (bind [this goal] this))

(defn zero [state] (Board. [] (queue) [(map->Grave state)]))
(defn unit [state] (Board. [state] (queue) []))
(def alpha (State. {} ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; conjunction and disjunction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro goal-form {:style/indent 1} [desc body]
  `(Goal. ~desc (~'fn ~'[{:as state :keys [smap done]}] ~body)))

(def g1 (goal-form :t (unit state)))
(def g0 (goal-form :f (zero state)))

(defn &
  ([] g1)
  ([g] g)
  ([g & gs]
   (goal-form (list* '& (:desc g) (map :desc gs))
     (reduce bind (bind state g) gs))))

(defn |
  ([] g0)
  ([g] g)
  ([g & gs]
   (let [gs (cons g gs)]
     (goal-form (cons '| (map :desc gs))
       (Board. [] (mapq (partial ->Thunk state) gs) [])))))

(defn all [gs] (apply & gs))
(defn any [gs] (apply | gs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; goals and constraints ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; === : Term , Term -> Goal

(defn === [u v]
  (goal-form (list '=== u v)
    (if-let [smap (unify u v smap)]
      (unit (assoc state :smap smap))
      (zero state))))

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defn pull [board]
  (loop [{:keys [state* thunk*] :as board} board]
    (cond (seq state*) (concat state* (lazy-seq (pull (update board :state* empty))))
          (seq thunk*) (recur (exec board)))))

(defn run
  ([goal] (run goal alpha))
  ([goal state] (pull (bind state goal))))

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
         (map :done)
         (map first)
         (map second)))

  )
