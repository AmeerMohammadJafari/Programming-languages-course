;; PL Project - Fall 2023
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (b)      #:transparent)  ;; a boolean constant, e.g., (bool #t)
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus (e1 e2)  #:transparent)  ;; subtract two expressions
(struct mult (e1 e2)  #:transparent)  ;; multiply two expressions
(struct div (e1 e2)  #:transparent)  ;; divide two expressions
(struct neg (e)  #:transparent)  ;; negate an expression
(struct andalso (e1 e2)  #:transparent)  ;; and two expressions
(struct orelse (e1 e2)  #:transparent)  ;; or two expressions
(struct cnd (e1 e2 e3)  #:transparent)  ;; if e1 then e2 else e3
(struct iseq (e1 e2)  #:transparent)  ;; if e1 is equal to e2 then true else false
(struct isls (e1 e2))
(struct isgt (e1 e2))


(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct tlam  (nameopt formal arg-type body) #:transparent) ;; a typed argument, recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application
(struct with (s e1 e2)         #:transparent) ;; with s = e1 in e2

(struct apair (e1 e2)       #:transparent) ;; a pair of expressions
(struct 1st (e1)       #:transparent) ;; first element of a pair
(struct 2nd (e1)       #:transparent) ;; second element of a pair


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent) ;; a letrec expression for recursive definitions

;; Type structures
;; Primitive types are: "int", "bool" and "null"
(struct collection (type) #:transparent) ;; collection of a certain type, e.g., (collection "int")
(struct function (input-type output-type) #:transparent) ;; e.g. (function ("int" int")) means fn f "int" -> "int"

;; Problem 1

(define (racketlist->numexlist xs)
  (cond [(null? xs) (munit)]
        [#t (apair (car xs) (racketlist->numexlist (cdr xs)))]
        ))


(define (numexlist->racketlist xs)
  (cond [(munit? xs) null]
        [(apair? xs)
         (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
        [#t (error "input is not a numex list")]
        ))


;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? str (caar env)) (cdar env)]
        [#t (envlookup (cdr env) str)]
        )
  )
(define (update-env env var val)
  (cond [(null? env) (cons (cons var val) null)]
        [(equal? var (caar env)) (cons (cons var val) (cdr env))]
        [#t (cons (car env) (update-env (cdr env) var val))]
        ))
;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]


        ; values evaluate to themselves
        [(num? e)
         (if (integer? (num-int e))
             e
             (error "NUMEX num should be integer constant"))]
        
        [(bool? e)
         (if (boolean? (bool-b e))
             e
             (error "NUMEX bool should be boolean constant"))]
        
        [(closure? e) e]
        [(munit? e) e]
        
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]

        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (cond [(and (num? v1)
                       (num? v2))
                  (num (quotient (num-int v1) 
                                 (num-int v2)))]
                 [(= (num-int v2) 0)
                  (error "NUMEX division by zero")]
                 (error "NUMEX division applied to non-number")))]

        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)]) ; short circuiting
           (if (bool? v1)
               (if (not (bool-b v1))
                   (bool #f)
                   (let ([v2 (eval-under-env (andalso-e2 e) env)])
                     (if (bool? v2)
                         (if (bool-b v2)
                             (bool #t)
                             (bool #f))
                         (error "NUMEX andalso applied to non-boolean"))))
               (error "NUMEX andalso applied to non-boolean")))]

        [(orelse? e) 
         (let ([v1 (eval-under-env (orelse-e1 e) env)]) ; short circuiting
           (if (bool? v1)
               (if (bool-b v1)
                   (bool #t)
                   (let ([v2 (eval-under-env (orelse-e2 e) env)])
                     (if (bool? v2)
                         (if (not(bool-b v2))
                             (bool #f)
                             (bool #t))
                         (error "NUMEX orelse applied to non-boolean"))))
               (error "NUMEX orelse applied to non-boolean")))]

        [(neg? e)
         (let ([v (eval-under-env (neg-e e) env)])
           (cond [(num? v)
                  (num (- (num-int v)))]
                 [(bool? v)
                  (bool (not (bool-b v)))]
                 [#t (error "NUMEX orelse applied to non-integer or non-boolean")]))]

        [(cnd? e) 
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (cond [(not (bool? v1)) (error "NUMEX condition applied to non-boolean")]
                 [(bool-b v1) (eval-under-env (cnd-e2 e) env)]
                 [#t (eval-under-env (cnd-e3 e) env)]))]

        [(iseq? e)
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (cond [(and (num? v1) (num? v2))
                  (bool (= (num-int v1) (num-int v2)))]
                 [(and (bool? v1) (bool? v2))
                  (bool (equal? (bool-b v1) (bool-b v2)))]
                 [(and (num? v1) (bool? v2))
                  (bool #f)]
                 [(and (bool? v1) (num? v2))
                  (bool #f)]
                 [#t (error "NUMEX iseq applied to non-integer or non-boolean")]))]
        [(isls? e)
         (let ([v1 (eval-under-env (isls-e1 e) env)]
               [v2 (eval-under-env (isls-e2 e) env)])
           (cond
             [(and (num? v1) (num? v2))
              (bool (< (num-int v1) (num-int v2)))]
             [#t (error "NUMEX isls applied to non-integer")]))]
        
        [(isgt? e)
         (let ([v1 (eval-under-env (isgt-e1 e) env)]
               [v2 (eval-under-env (isgt-e2 e) env)])
           (cond
             [(and (num? v1) (num? v2))
              (bool (> (num-int v1) (num-int v2)))]
             [#t (error "NUMEX isgt applied to non-integer")]))]


        [(with? e) 
         (let ([v1 (eval-under-env (with-e1 e) env)]
               [s (with-s e)])
           (eval-under-env (with-e2 e) (update-env env s v1)))]

        [(lam? e)
         (closure env e)]

        [(apply? e)
         (let ([v1 (eval-under-env (apply-funexp e) env)])
           (cond [(closure? v1)
                  (let ([v2 (eval-under-env (apply-actual e) env)]
                        [l (closure-f v1)])
                    (let ([env (update-env (closure-env v1) (lam-formal l) v2)])
                      (if (null? (lam-nameopt l))
                          (eval-under-env (lam-body l) env)
                          (eval-under-env (lam-body l) (update-env env (lam-nameopt l) v1)))
                      ))]
                 [(lam? v1)  ;; For letrec
                  (eval-under-env (apply v1 (apply-actual e)) env)]
                 [#t (error "NUMEX apply applied to a non-function" v1)]))]

        [(apair? e) 
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]

        [(1st? e)
         (let ([v1 (eval-under-env (1st-e1 e) env)])
           (cond [(apair? v1) (apair-e1 v1)]
                 [#t (error "NUMEX 1st applied to non-apair")]))]

        [(2nd? e)
         (let ([v1 (eval-under-env (2nd-e1 e) env)])
           (cond [(apair? v1) (apair-e2 v1)]
                 [#t (error "NUMEX 2nd applied to non-apair")]))]

        [(ismunit? e)
         (let ([v (eval-under-env (ismunit-e e) env)])
           (cond [(munit? v) (bool #t)]
                 [#t (bool #f)]))]

        [(letrec? e)
         (let ([e1 (letrec-e1 e)]
               [e2 (letrec-e2 e)]
               [e3 (letrec-e3 e)]
               [e4 (letrec-e4 e)]
               [s1 (letrec-s1 e)]
               [s2 (letrec-s2 e)]
               [s3 (letrec-s3 e)]
               [s4 (letrec-s4 e)]
               [e5 (letrec-e5 e)])
           (let ([env (update-env (update-env (update-env (update-env env s4 e4)
                                                          s3 e3)
                                              s2 e2)
                                  s1 e1)])
             (let ([v1 (eval-under-env e1 env)]
                   [v2 (eval-under-env e2 env)]
                   [v3 (eval-under-env e3 env)]
                   [v4 (eval-under-env e4 env)])
               (eval-under-env (with s1 v1
                                     (with s2 v2
                                           (with s3 v3
                                                 (with s4 v4 e5)))) env))))]

        [(key? e)
         (if (string? (key-s e))
             (let ([v2 (eval-under-env (key-e e) env)])
               (key (key-s e) v2))
             (error "NUMEX key applied to non-string"))]

        [(record? e)
         (let ([k (eval-under-env (record-k e) env)]
               [r (eval-under-env (record-r e) env)])
           (if (key? k)
               (if (or (munit? r) (record? r))
                   (record k r)
                   (error "NUMEX record applied to non-record or munit"))
               (error "NUMEX record applied to non-key")))]

        [(value? e)
         (if (string? (value-s e))
             (let ([r (eval-under-env (value-r e) env)])
               (if (record? r)
                   (cond [(equal? (key-s (record-k r)) (value-s e)) (key-e (record-k r))]
                         [(munit? (record-r r)) (munit)]
                         [#t (eval-under-env (value (value-s e) (record-r r)) env)])
                   (error "NUMEX value applied to non-record")))
             (error "NUMEX value applied to non-string"))]
             
        
        [(string? e) e]
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))

;; Problem 3
;; Complete more cases for other kinds of NUMEX expressions.
;; We will test infer-under-env by calling its helper function, infer-exp.
(define (infer-under-env e env)
  (cond [(var? e) 
         (infer-under-env (envlookup env (var-string e)) env)]
        [(munit? e) "null"]

        [(plus? e) 
         (let ([t1 (infer-under-env (plus-e1 e) env)]
               [t2 (infer-under-env (plus-e2 e) env)])
           (if (and (equal? "int" t1)
                    (equal? "int" t2))
               "int"
               (error "NUMEX TYPE ERROR: addition applied to non-integer")))]

        [(num? e)
         (cond
           [(integer? (num-int e)) "int"]
           [#t (error "NUMEX TYPE ERROR: num should be a constant number")])]

        [(bool? e)
         (cond
           [(boolean? (bool-b e)) "bool"]
           [#t (error "NUMEX TYPE ERROR: bool should be #t or #f")])]

        [(andalso? e)
            (let ([t1 (infer-under-env (andalso-e1 e) env)]
                    [t2 (infer-under-env (andalso-e2 e) env)])
                    (if (and (equal? "bool" t1)
                             (equal? "bool" t2))
                        "bool"
                (error "NUMEX TYPE ERROR: andalso applied to non-boolean")))]
        
        [(neg? e)
        (let ([t1 (infer-under-env (neg-e e) env)])
            (cond ((equal? "bool" t1) "bool")
                ((equal? "int" t1) "int")
            (#t (error "NUMEX TYPE ERROR: neg applied to non-boolean or non-integer"))))]

        [(cnd? e)
         (let ([t1 (infer-under-env (cnd-e1 e) env)]
               [t2 (infer-under-env (cnd-e2 e) env)]
               [t3 (infer-under-env (cnd-e3 e) env)])
           (if (and (equal? "bool" t1)
                    (equal? t2 t3))
               t2
               (error "NUMEX TYPE ERROR: cnd applied to non-boolean or non-matching types")))]

        [(iseq? e)
         (let ([t1 (infer-under-env (iseq-e1 e) env)]
               [t2 (infer-under-env (iseq-e2 e) env)])
           (if (and(equal? t1 t2) (or (equal? t1 "bool") (equal? t1 "int")))
               "bool"
               (error "NUMEX TYPE ERROR: iseq applied to non-matching types")))]
        [(isls? e)
         (let ([t1 (infer-under-env (isls-e1 e) env)]
               [t2 (infer-under-env (isls-e2 e) env)])
           (if (and(equal? t1 t2) (equal? t1 "int"))
               "bool"
               (error "NUMEX TYPE ERROR: isls applied to non-matching types")))]
        [(isgt? e)
         (let ([t1 (infer-under-env (isgt-e1 e) env)]
               [t2 (infer-under-env (isgt-e2 e) env)])
           (if (and(equal? t1 t2) (equal? t1 "int"))
               "bool"
               (error "NUMEX TYPE ERROR: isgt applied to non-matching types")))]
        

        [(with? e)
         (let ([t1 (infer-under-env (with-e1 e) env)])
           (infer-under-env (with-e2 e) (cons (cons (with-s e) t1) env)))]

        [(tlam? e)
         (let ([t1 (infer-under-env (tlam-body e) (cons (cons (tlam-formal e) (tlam-arg-type e)) env))])
               (function (tlam-arg-type e) t1))]

        [(apply? e)
         (let ([t1 (infer-under-env (apply-funexp e) env)]
               [t2 (infer-under-env (apply-actual e) env)])
           (if (function? t1)
               (if (equal? t2 (function-input-type t1))
                   (function-output-type t1)
                   (error "NUMEX TYPE ERROR: apply applied to non-matching types"))
                (error "NUMEX TYPE ERROR: apply applied to non-function")))]

      [(apair? e)
       (let ([t1 (infer-under-env (apair-e1 e) env)]
             [t2 (infer-under-env (apair-e2 e) env)])
             (cond ((equal? t2 "null") (collection t1))
                   ((collection? t2)  
                            (if (equal? t1 (collection-type t2))
                            (collection t1)
                            (error "NUMEX TYPE ERROR: apair applied to non-matching types")))
                     (#t (error "NUMEX TYPE ERROR: apair applied to non-collection"))))] 

     [(1st? e)
     (let ([t1 (infer-under-env (1st-e1 e) env)])  
        (if (collection? t1)
            (collection-type t1)
            (error "NUMEX TYPE ERROR: 1st applied to non-collection")))]

     [(2nd? e)
     (let ([t1 (infer-under-env (2nd-e1 e) env)])  
        (if (collection? t1)
            t1
            (error "NUMEX TYPE ERROR: 2nd applied to non-collection")))]

    [(ismunit? e)
    (let ([t1 (infer-under-env (ismunit-e e) env)])
        (if (or (collection? t1) (equal? t1 "null"))
            "bool"
            (error "NUMEX TYPE ERROR: ismunit applied to non-collection")))]  
        ;; CHANGE add more cases here
        [(string? e) e]
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (infer-exp e)
  (infer-under-env e null))

;; Problem 4

(define (ifmunit e1 e2 e3)
  (cnd (ismunit e1)
       e2
       e3))

(define (with* bs e2)
  (cond [(null? bs) e2]
        [#t (with (caar bs) (cdar bs) (with* (cdr bs) e2))]
        ))

(define (ifneq e1 e2 e3 e4)
  (with "_x" e1
        (with "_y" e2
              (cnd (iseq (var "_x") (var "_y"))
                   e4
                   e3))))

;; Problem 5

(define numex-fold
  (lam "fun1" "f"
       (lam null "acc"
            (lam null "ls"
                 (ifmunit (var "ls") (var "acc")
                          (with "_x" (apply (var "f") (1st (var "ls")))
                                      (apply (var "_x") (apply (apply (apply (var "fun1")(var "f")) (var "acc")) (2nd(var "ls"))))))))))
                                  

(define numex-concat
  (with "fold" numex-fold
       (lam null "xs"
            (lam null "ys"
                (with "pair" (lam null "x" (lam null "y" (apair (var "x") (var "y"))))
                 (apply (apply(apply (var "fold") (var "pair"))(var "ys"))(var "xs")))

        ))))

(define numex-bind
  (with "concat" numex-concat
        (lam "fun1" "f"
             (lam null "ls"
                (ifmunit (var "ls") (munit)  
                   (apply
                     (apply (var "concat") (apply(var "f")(1st(var "ls"))))
                            (apply (apply(var "fun1")(var "f"))(2nd(var "ls"))))       
        )))))

;; Problem 6

(define type-error-but-evaluates-ok
  (cnd (bool #t)
       (bool #t)
       (num 1))
  )

;; results in addition of num and munit
(define type-ok-but-evaluates-error
  (plus (num 1)
        (1st
         (2nd
          (apair (num 1) (munit))))))

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))