#lang racket
(require redex)

;problem 1----------------------------------------------------------------------------------------------

(define-language mobile
  (m w        ; atomic sculpture (weight)
     (m m w)) ; composite
  (w number)) ; weight is a number 

;5 sample mobiles
(define sample-mobile-1 1)
(define sample-mobile-2 '(1 1 2))
(define sample-mobile-3 '((1 1 2) (1 1 2) 3))
(define sample-mobile-4 '(((1 1 2) (1 1 2) 3) (1 1 2) 4))
(define sample-mobile-5 '(((1 1 2) (1 1 2) 3) ((1 (1 1 2) 3) 1 3) 4))

;metafunctions
(define-metafunction mobile
  num-atomics : m -> natural 
  [(num-atomics w) 1]
  [(num-atomics (m_1 m_2 w)) ,(+ (term (num-atomics m_1)) (term (num-atomics m_2)))]
)

(define-metafunction mobile
  total-weight : m -> natural 
  [(total-weight w) w]
  [(total-weight (m_1 m_2 w)) ,(+ (term (total-weight m_1)) (term (total-weight m_2)) (term w))]
)

(define-metafunction mobile
  depth : m -> natural 
  [(depth w) 0]
  [(depth (m_1 m_2 w)) ,(+ (max (term (depth m_1)) (term (depth m_2))) 1)]
)

(define-metafunction mobile
  replace : m w w -> m 
  [(replace w_1 w_1 w_2) w_2]
  [(replace (m_1 m_2 w_1) w_1 w_2) ((replace m_1 w_1 w_2) (replace m_2 w_1 w_2) w_2)]
  [(replace (m_1 m_2 w_3) w_1 w_2) ((replace m_1 w_1 w_2) (replace m_2 w_1 w_2) w_3)]
  [(replace m w_1 w_2) m]
)

;according to def in the problem set, but it makes for a lousy mobile...
(define-metafunction mobile
  balanced? : m -> boolean
  [(balanced? w) #true] 
  [(balanced? (m_1 m_2 w_b)) ,(= (term (total-weight m_1)) (term (total-weight m_2)))]
)

;this is more intuitive
(define-metafunction mobile
  rec-balanced? : m -> boolean
  [(rec-balanced? w) #true]    
  [(rec-balanced? (m_1 m_2 w_b)) ,(and
                                   (= (term (total-weight m_1)) (term (total-weight m_2)))
                                   (and (term (rec-balanced? m_1)) (term (rec-balanced? m_2))))]
)

;problem 2----------------------------------------------------------------------------------------------

(define-language Graph
  (g (graph n ... e ...))
  (n (node x))
  (e (edge x x))
  (x variable-not-otherwise-mentioned))
 
(define g1 (term (graph (node a) (node b) (node c)
                        (edge b a) (edge b c))))
(define g2 (term (graph (node a) (node b)
                        (edge b a) (edge b c))))

; checks whether there are any nodes within a list named using a particular variable
(define-metafunction Graph
  var-in-nodes : x n ... -> boolean
  [(var-in-nodes x (node x) n_l ...) #true]
  [(var-in-nodes x (node x_x) n_l ...) (var-in-nodes x n_l ...)]
  [(var-in-nodes x) #false]
)

; checks whether a graph contains only edges which refer to nodes within that graph
(define-metafunction Graph
  good : g -> boolean
  ; there is a graph with at least one edge and some nodes
  [(good (graph n_l ... (edge x_1 x_2) e_l ...))
         ,(if
           ; if this edge only contains known nodes
           (and (term (var-in-nodes x_1 n_l ...))
                (term (var-in-nodes x_2 n_l ...)))
           ; then continue checking edges
           (term (good (graph n_l ... e_l ...)))
           ; otherwise the graph is not good
           #false
          )]
  ; you checked all the edges and you're still up -> the graph is good
  ; also: a graph with no edges is always good
  [(good (graph n_l ...)) #true])

;problem 3----------------------------------------------------------------------------------------------

(define-language language-one
  (Expression Variable (function Variable Expression) (Expression Expression))
  (Variable string))

(define-language language-two
  (DBExpression Number Variable (function Variable DBExpression) (DBExpression DBExpression))
  (Number number)
  (Variable string))

(define language-one-example
  (term (function "y"
    ((function "x"
       ("x" "y"))
      ("x" "y")))))

(define language-two-example
  (term (function "y"
    ((function "x"
       (0 1))
      ("x" 0)))))

; USELESS helper functions for a pairlist
(define (increment pairlist)
  (map (lambda (x) (cons (car x) (+ (cdr x) 1))) pairlist))

(define (insert pairlist key value)
  (if (empty? pairlist)
      (cons (cons key value) pairlist)
      (if (string=? (car (car pairlist)) key)
          (cons (cons key value) (cdr pairlist))
          (cons (car pairlist) (insert (cdr pairlist) key value)))))

(define (in-domain? pairlist key)
  (if (empty? pairlist)
      #false
      (if (string=? (car (car pairlist)) key)
          #true
          (in-domain? (cdr pairlist) key))))

(define (retrieve pairlist key)
  (if (empty? pairlist)
      'error
      (if (string=? (car (car pairlist)) key)
          (cdr (car pairlist))
          (retrieve (cdr pairlist) key))))

; language union with pairlist, because metafunctions need them
(define-union-language language-chimera language-one language-two)
(define-extended-language language-chimera-with-distance language-chimera (Pair (Variable Number)))

; helper meta-functions for distance
(define-metafunction language-chimera-with-distance
  ;retrieve-or-return-self : Pair ... Variable -> (union Number Variable) ; <- don't know how to express this
  [(retrieve-or-return-self Variable) Variable]
  [(retrieve-or-return-self (Variable Number) Pair ... Variable) Number]
  [(retrieve-or-return-self Pair_h Pair ... Variable) (retrieve-or-return-self Pair ... Variable)])

(define-metafunction language-chimera-with-distance
  increment-all : (Pair ...) -> (Pair ...)
  [(increment-all ()) ()]
  [(increment-all ((Variable Number))) ((Variable ,(+ (term Number) 1)))]
  [(increment-all ((Variable Number) Pair ...)) ,(cons (term (Variable ,(+ (term Number) 1))) (term (increment-all (Pair ...))))])

(define-metafunction language-chimera-with-distance
  set-one-to-zero : Variable (Pair ...) -> (Pair ...)
  [(set-one-to-zero Variable ((Variable Number) Pair ...)) ((Variable 0) Pair ...)]
  [(set-one-to-zero Variable (Pair_h Pair_t ...)) ,(cons (term Pair_h) (term (set-one-to-zero Variable (Pair_t ...))))]  
  [(set-one-to-zero Variable ()) ((Variable 0))])

; translate Expression with distances:
;
; function Variable Expression with distances
; --> function Variable <translate Expression with distances[forall z in dom(distances) z maps to distances(x) + 1][x maps to 0]>
;
; (Expression_1 Expression_2) with distances
; --> (<translate Expression_1 with distances> <translate Expression_1 with distances>)
;
; Variable with distances where Variable in dom(distances)
; --> distances(Variable)
;
; Variable with distances where Variable not in dom(distances)
; --> Variable

; coup de grace:
(define-metafunction language-chimera-with-distance
  translate-one-to-two : Expression (Pair ...) -> DBExpression
  ; Definition
  [(translate-one-to-two (function Variable Expression) (Pair ...))
   (function Variable
             (translate-one-to-two
              Expression
              (set-one-to-zero Variable (increment-all (Pair ...)))))]
  ; Application
  [(translate-one-to-two (Expression_1 Expression_2) (Pair ...))
   ((translate-one-to-two Expression_1 (Pair ...))
    (translate-one-to-two Expression_2 (Pair ...)))]
  ; Variable (both cases)
  [(translate-one-to-two Variable (Pair ...)) (retrieve-or-return-self Pair ... Variable)]
)

; syntactic suger for coup de grace
(define-metafunction language-chimera-with-distance
  to-debruijn : Expression Pair ... -> DBExpression
  [(to-debruijn Expression Pair ...) (translate-one-to-two Expression (Pair ...))]
)