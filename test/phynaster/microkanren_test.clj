(ns phynaster.microkanren-test
  (:require [clojure.test :refer :all]
            [phynaster.core-test :refer [$]]
            [phynaster.microkanren :refer :all]))

(deftest test-unification
  ($ (run* [q]
       (=== q 1))
     '({:q 1})
     "q = 1
")
  ($ (run* [p q]
       (=== p q)
       (=== q 1))
     '({:p 1, :q 1})
     "p = q = 1
")
  ($ (run* [q]
       (=== q 1)
       (=== q 2))
     '()
     "q = 1 = 2 impossible
"))

(deftest test-free-lvar
  ($ (run* [p q]
       (=== p q))
     '({:p ?0, :q ?0})
     "p = q
")
  ($ (run* [p q r]
       (=== p q))
     '({:p ?0, :q ?0, :r ?1})
     "p = q, r
"))

(deftest test-conso
  ($ (run* [p q]
       (=== (cons p q) [1 2 3]))
     '({:p 1, :q (2 3)})
     "(p . q) = [1 2 3]
")
  ($ (run* [p q]
       (=== (cons 1 p) q))
     '({:p ?0, :q (1 . ?0)})
     "(1 . p) = q with improper tail
"))

(deftest test-appendo
  ($ (run* [r]
       (appendo [1 2] [3 4] r))
     '({:r (1 2 3 4)})
     "[1 2] ++ [3 4] = r
")
  ($ (run* [p q]
       (appendo p q [1 2 3 4]))
     '({:p (), :q (1 2 3 4)}
       {:p (1), :q (2 3 4)}
       {:p (1 2), :q (3 4)}
       {:p (1 2 3), :q (4)}
       {:p (1 2 3 4), :q ()})
     "p ++ q = [1 2 3 4]
")
  ($ (run 4 [p q r]
       (appendo p q r))
     '({:p (), :q ?0, :r ?0}
       {:p (?0), :q ?1, :r (?0 . ?1)}
       {:p (?0 ?1), :q ?2, :r (?0 ?1 . ?2)}
       {:p (?0 ?1 ?2), :q ?3, :r (?0 ?1 ?2 . ?3)})
     "p ++ q = r
"))
