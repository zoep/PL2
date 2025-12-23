(declare-const balance_pre (Array (_ BitVec 64) (_ BitVec 64)))
(declare-const balance_post (Array (_ BitVec 64) (_ BitVec 64)))

(declare-const to (_ BitVec 64))
(declare-const from (_ BitVec 64))
(declare-const amt (_ BitVec 64))
(declare-const size (_ BitVec 64))

(define-fun pathcond1 () Bool
    (and (and (bvule (_ bv0 64) amt) (bvult to size)) (bvult from size)))

(define-fun pathcond2 () Bool
    (bvule (select balance_pre from) amt))


(define-fun pathcond3 () Bool
    (not (= from (_ bv42 64))))


;; PATHCONDITIONS
(assert (= pathcond1 true))
(assert (= pathcond2 true))
(assert (= pathcond3 true))

;; POSTSTATE
(assert (= (select balance_post from) (bvsub (select balance_pre from) amt)))
(assert (= (select balance_post to) (bvadd (select balance_pre to) amt)))

;; QUERY
(assert (not (and (= (select balance_post from) (bvsub (select balance_pre from) amt))
                  (= (select balance_post to) (bvadd (select balance_pre to) amt)))))


(check-sat)
