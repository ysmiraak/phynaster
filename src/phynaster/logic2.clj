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

(def empty-queue clojure.lang.PersistentQueue/EMPTY)
(defn mapq [f xs] (into empty-queue (map f xs)))

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
;; bind : Thunk , Goal -> Thunk
;; bind : State , Goal -> Board
;; bind : Board , Goal -> Board
;;
;; plus : Board , Board+ -> Board
;;
;; pull : Board -> State*
;; exec : Board -> Board
;; exec : Thunk -> Board
;; call : Goal -> Thunk -> Thunk
;; call : Goal -> State -> Board
;; call : Goal -> Board -> Board

(defprotocol IBind (bind [this goal]))
(defprotocol IPlus (plus [this that+]))
(defprotocol IPull (pull [this]))
(defprotocol IExec (exec [this]))
(defprotocol ICall (call [this]))
(defprotocol IUnit (unit [this]))

(defrecord Goal [desc cont]
  ICall
  (call [this] (fn [that] (bind that this))))

(defrecord Board [state* thunk*]
  IBind
  (bind [this goal]
    (let [{state* true graves false} (group-by :alive state*)]
      (plus (Board. graves (mapq (call goal) thunk*))
            (map (call goal) state*))))
  IPlus
  (plus [this that+]
    (Board. (into state* (mapcat :state* that+))
            (into thunk* (mapcat :thunk* that+))))
  IExec
  (exec [this]
    (if (seq thunk*)
      ;; force thunks in cycle, this is where magic happens
      ;; 0. given a model : Thunk -> Logit
      ;; 1. assign a logit priority to each thunk
      ;; 2. exec thunk with the highest priority
      ;; 3. repeat from 2 til no more thunks
      ;; 4. update model by the alive likelihood
      (plus (update this :thunk* pop)
            [(exec (peek  thunk*))])
      this))
  IPull
  (pull [this]
    (loop [{:keys [state* thunk*] :as this} this]
      (cond (seq state*) (concat state* (lazy-seq (pull (update this :state* empty))))
            (seq thunk*) (recur (exec this))))))

(declare &)
(defrecord Thunk [state goal]
  IBind
  (bind [this goal'] (Thunk. state (& goal goal')))
  IExec
  (exec [this] (bind state goal)))

(defrecord State [alive smap done]
  IBind
  (bind [this {:keys [desc cont]}]
    (if alive
      (cont (update this :done conj desc))
      (unit this)))
  IUnit
  (unit [this] (Board. [this] empty-queue)))

(def initial-state (State. true {} () 0))
(def initial-board (unit initial-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; conjunction and disjunction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def g1 (Goal. :t (fn [state] (unit state))))
(def g0 (Goal. :f (fn [state] (unit (assoc state :alive false)))))

(defn &
  ([] g1)
  ([g] g)
  ([g & gs]
   (Goal. (list* '& (:desc g) (map :desc gs))
          (fn [state]
            (reduce bind (bind state g) gs)))))

(defn |
  ([] g0)
  ([g] g)
  ([g & gs]
   (let [gs (cons g gs)]
     (Goal. (cons '| (map :desc gs))
            (fn [state]
              (Board. [] (mapq (partial ->Thunk state) gs)))))))

(defn all [gs] (apply & gs))
(defn any [gs] (apply | gs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; goals and constraints ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; === : Term , Term -> Goal

(defn === [u v]
  (Goal. (list '=== u v)
         (fn [{:as state :keys [smap]}]
           (unit (if-let [smap (unify u v smap)]
                   (assoc state :smap smap)
                   (assoc state :alive false))))))

;;;;;;;;;;;;;;;;;;;;
;; user interface ;;
;;;;;;;;;;;;;;;;;;;;

(defn run
  ([goal] (run goal initial-state))
  ([goal state] (pull ((:cont goal) state))))

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
