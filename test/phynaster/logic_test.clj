(ns phynaster.logic-test
  (:require [clojure.test :refer :all]
            [phynaster.core-test :refer [$]]
            [phynaster.logic :refer :all]))

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
")
  ($ (run* [p q]
       (exist [r]
         (=== p [1 r])
         (=== q [r 2])))
     '({:p (1 ?0), :q (?0 2)})
     "p = [1 r], q = [r 2]
"))

(deftest test-=cons
  ($ (run* [p q]
       (=cons p q [1 2 3]))
     '({:p 1, :q (2 3)})
     "(p . q) = [1 2 3]
")
  ($ (run* [p q]
       (=cons 1 p q))
     '({:p ?0, :q (1 . ?0)})
     "(1 . p) = q with improper tail
"))

(deftest test-=append
  ($ (run* [r]
       (=append [1 2] [3 4] r))
     '({:r (1 2 3 4)})
     "[1 2] ++ [3 4] = r
")
  ($ (run* [p q]
       (=append p q [1 2 3 4]))
     '({:p (), :q (1 2 3 4)}
       {:p (1), :q (2 3 4)}
       {:p (1 2), :q (3 4)}
       {:p (1 2 3), :q (4)}
       {:p (1 2 3 4), :q ()})
     "p ++ q = [1 2 3 4]
")
  ($ (run 4 [p q r]
       (=append p q r))
     '({:p (), :q ?0, :r ?0}
       {:p (?0), :q ?1, :r (?0 . ?1)}
       {:p (?0 ?1), :q ?2, :r (?0 ?1 . ?2)}
       {:p (?0 ?1 ?2), :q ?3, :r (?0 ?1 ?2 . ?3)})
     "p ++ q = r
"))

(deftest test-=insert
  ($ (run* [q]
       (=insert 1 [0 2] [0 q 2]))
     '({:q 1})
     "insert 1 into [0 2] as [0 q 2]
")

  ($ (run* [q]
       (=insert 1 [0 2] q))
     '({:q (1 0 2)}
       {:q (0 1 2)}
       {:q (0 2 1)})
     "insert 1 into [0 2] as q
")
  ($ (run 4 [p q r]
       (=insert p q r))
     '({:p ?0, :q ?1, :r (?0 . ?1)}
       {:p ?0, :q (?1 . ?2), :r (?1 ?0 . ?2)}
       {:p ?0, :q (?1 ?2 . ?3), :r (?1 ?2 ?0 . ?3)}
       {:p ?0, :q (?1 ?2 ?3 . ?4), :r (?1 ?2 ?3 ?0 . ?4)})
     "insert p into q as r
"))

(deftest test-=!=
  ($ (run* [p q]
       (=== p 1)
       (=!= p 1))
     '()
     "=!= after ===
")
  ($ (run* [p q]
       (=!= p 1)
       (=== p 1))
     '()
     "=!= before ===
")
  ($ (run* [p q]
       (=== p 1)
       (=!= p q)
       (=== q 1))
     '()
     "=!= between ===
")
  ($ (run* [p x y]
       (=!= [5 6] p)
       (=== [x y] p)
       (=== 5 x)
       (=== 6 y))
     '()
     "=!= on sequence
")
  ($ (run* [p x y]
       (=!= [5 6] p)
       (=== [x y] p)
       (=== 5 x)
       (=== 7 y))
     '({:p (5 7), :x 5, :y 7})
     "=!= succeed
"))

(deftest test-=rember
  ($ (run* [q]
       (=rember 'b '(a b c b d) q))
     '({:q (a c b d)})
     "rember only first occurence
")
  ($ (run* [q]
       (=rember 'b '(b) '(b)))
     '()
     "rember at least one
")
  ($ (run* [q]
       (exist [x out]
         (=rember x '(a b c) out)
         (=== [x out] q)))
     '({:q (a (b c))}
       {:q (b (a c))}
       {:q (c (a b))}
       {:q (?0 (a b c))})
     "rember with reified constraints
TODO (=!= ?0 c) (=!= ?0 b) (=!= ?0 a)
"))
