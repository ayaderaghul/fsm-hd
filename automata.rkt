#lang racket
(require racket/hash)
(provide (all-defined-out))

(define ACTIONS# 2)
(define ACTIONS (list 'D 'H))
(define (random-action)
  (list-ref ACTIONS (random ACTIONS#)))

(struct automaton (head body) #:transparent)
; body is a hash table of states
(struct state (action dispatch) #:transparent)

(define (make-random-automaton states#)
  (define initial-current (random states#))
  (define to-detach (random states#))
  (define (make-head) (hash 'INITIAL initial-current
                            'CURRENT initial-current
                            'PAYOFF 0
                            ))
  (define ids (build-list states# values))
  (define (make-body) (apply hash (flatten (map list ids (make-states)))))
  (define (make-states) (build-list states# make-state))
  (define (make-state _) (state (random-action) (make-transition)))
  (define (make-transition)
    (hash 'D (random states#)
          'H (random states#)))
  (automaton (make-head) (make-body)))

(define (reset a) ; reset
  (match-define (automaton head body) a)
  (define new-head*
    (hash-set head 'CURRENT (hash-ref head 'INITIAL)))
  (define new-head
    (hash-set new-head* 'PAYOFF 0))
  (automaton new-head body))

(define (reset-machine m)
  (match-define (cons o i) m)
  (cons (reset o) (reset i)))

(define (make-random-machine s1 s2)
  (define owner (make-random-automaton s1))
  (define intruder (make-random-automaton s2))
  (cons owner intruder))

(define (retrieve-payoff m)
  (match-define (cons owner intruder) m)
  (define (retrieve-automaton-payoff au)
    (hash-ref (automaton-head au) 'PAYOFF))
  (define o (retrieve-automaton-payoff owner))
  (define i (retrieve-automaton-payoff intruder))
  (cond [(> o i) o]
        [(< o i) i]
        [(= o i) o]))


;; CLASSIC AUTOMATA
(define (hawk)
  (define head (hash 'INITIAL 0 'CURRENT 0 'PAYOFF 0))
  (define body (hash 0 (state 'H (hash 'D 0 'H 0))))
  (automaton head body))

(define (dove)
  (define head (hash 'INITIAL 0 'CURRENT 0 'PAYOFF 0))
  (define body (hash 0 (state 'D (hash 'D 0 'H 0))))
  (automaton head body))

(define (doves)
  (cons (dove) (dove)))
(define (hawks)
  (cons (hawk) (hawk)))

(define (earner)
  (cons (hawk) (dove)))
(define (robber)
  (cons (dove) (hawk)))
(define d (doves))
(define h (hawks))
(define e (earner))
(define r (robber))



;;IMMUTABLE MUTATION
(define (mutate-marginally a)
  (match-define (automaton head body) a)
  (define l (hash-count body))
  (define mutate-initial (random l))
  (define mutate-state (random l))
  (match-define (state action dispatch) (hash-ref body mutate-state))
  (define r (random 3))
  (define new-head
    (cond [(zero? r) (hash-set head 'INITIAL mutate-initial)]
          [else head])) ; leave unchanged
  (define new-body
    (cond [(zero? r) body] ; leave unchanged
          [(= r 1)
           (hash-set body mutate-state
                     (state (random-action) dispatch))]
          [(= r 2)
           (hash-set body mutate-state
                     (state action
                            (hash-set dispatch (random-action) (random l))))]))
  (automaton new-head new-body))

(define (add-state a)
  (match-define (automaton head body) a)
  (define l (hash-count body))
  (define (make-transition)
    (hash 'D (random (+ l 1))
          'H (random (+ l 1))))
  (define (make-state) (state (random-action) (make-transition)))
  (define mutate-state (random l))
  (match-define (state action dispatch) (hash-ref body mutate-state))
  (define new-body
    (hash-union
     (hash-set body mutate-state
              (state action
                     (hash-set dispatch (random-action) l)))
     (hash l (make-state))))
  (automaton head new-body))

(define (random-mem l)
  (list-ref l (random (length l))))

;; for detach and add state, use mutable would be much shorter

(define (detach-state a)
  (match-define (automaton head body) a)
  (define l (hash-count body))
  (cond
   [(= l 1) (mutate-marginally a)]
   [else (begin
           (define (random-but n r)
             (random-mem (remq mutate-state (build-list n values))))
           (define mutate-state (random l))
           (define (check-rule rule)
             (match-define (cons opponent-action reaction) rule)
             (if (= mutate-state reaction)
                 (cons opponent-action (random-but l mutate-state))
                 rule))
           (define (check-dispatch rules)
             (apply hash
                    (flatten
                     (map check-rule (hash->list rules)))))
           (define (check-state a-state)
             (match-define (state action rules) a-state)
             (struct-copy state a-state [dispatch (check-dispatch rules)]))
           (define new-body
             (for/list([i (in-range l)])
               (list i
                     (check-state (hash-ref body i)))))
           (automaton head (apply hash (flatten new-body))))]))

(define (mutate a)
  (define r (random 3))
  (cond [(zero? r) (mutate-marginally a)]
        [(= r 1) (add-state a)]
        [(= r 2) (detach-state a)]))

(define (mutate-machine m)
  (match-define (cons o i) m)
  (define r0 (random 2))
  (if (zero? r0)
      (cons (mutate o) i)
      (cons o (mutate i))))

(define (mutates au n)
  (cond [(zero? n) '()]
        [else
         (define new (mutate au))
         (cons au (mutates new (- n 1)))]))

;; INTERACTION: PAIR-MATCH
(define PAYOFF-TABLE
  (list
   (list (cons 3 3) (cons 1 5))
   (list (cons 5 1) (cons 0 0))))
(define (payoff action1 action2)
  (define (convert action)
    (for/last ([i (in-range ACTIONS#)]
      #:final (equal? action (list-ref ACTIONS i)))
      i))
  (list-ref (list-ref PAYOFF-TABLE (convert action1))
            (convert action2)))

;; continuation probability
(define (interact m1 m2 rounds delta)
  (match-define (cons o1 i1) m1)
  (match-define (cons o2 i2) m2)
  (define r1 (random 2))
  (define au1
    (if (zero? r1) ; agent 1 is owner
        o1 i1))
  (define au2
    (if (zero? r1) i2 o2))
  (match-define (automaton head1 body1) au1)
  (match-define (automaton head2 body2) au2)
  (define-values (next1 next2 pay1 pay2 round-results)
    (for/fold ([current1 (hash-ref head1 'CURRENT)]
               [current2 (hash-ref head2 'CURRENT)]
               [payoff1 (hash-ref head1 'PAYOFF)]
               [payoff2 (hash-ref head2 'PAYOFF)]
               [round-results '()])
              ([_ (in-range rounds)])
      #:final (> (random) delta)
      (match-define (state action1 dispatch1) (hash-ref body1 current1))
      (match-define (state action2 dispatch2) (hash-ref body2 current2))
      (match-define (cons pay1 pay2) (payoff action1 action2))
      (define n1 (hash-ref dispatch1 action2))
      (define n2 (hash-ref dispatch2 action1))
      (define round-result (list pay1 pay2))
      (values n1 n2
              (+ payoff1 (* pay1 (- 1 delta)))
              (+ payoff2 (* pay2 (- 1 delta)))
               ;(+ payoff1 pay1)
               ;(+ payoff2 pay2)
              (cons round-result round-results))))
  (values
   (reverse round-results)
   (if (zero? r1)
       (cons
        (automaton (hash-set head1 'PAYOFF (round5 pay1)) body1)
        i1)
       (cons
        o1
        (automaton (hash-set head1 'PAYOFF (round5 pay1)) body1)))
   (if (zero? r1)
       (cons
        o2
        (automaton (hash-set head2 'PAYOFF (round5 pay2)) body2))
       (cons
        (automaton (hash-set head2 'PAYOFF (round5 pay2)) body2)
        i2))
          ))

(define (interact-d m1 m2 rounds delta)
  (match-define (cons o1 i1) m1)
  (match-define (cons o2 i2) m2)
  (define r1 (random 2))
  (define au1
    (if (zero? r1) ; agent 1 is owner
        o1 i1))
  (define au2
    (if (zero? r1) i2 o2))
  (match-define (automaton head1 body1) au1)
  (match-define (automaton head2 body2) au2)
  (define-values (next1 next2 pay1 pay2 round-results)
    (for/fold ([current1 (hash-ref head1 'CURRENT)]
               [current2 (hash-ref head2 'CURRENT)]
               [payoff1 (hash-ref head1 'PAYOFF)]
               [payoff2 (hash-ref head2 'PAYOFF)]
               [round-results '()])
              ([_ (in-range rounds)])
      (match-define (state action1 dispatch1) (hash-ref body1 current1))
      (match-define (state action2 dispatch2) (hash-ref body2 current2))
      (match-define (cons pay1 pay2) (payoff action1 action2))
      (define n1 (hash-ref dispatch1 action2))
      (define n2 (hash-ref dispatch2 action1))
      (define round-result (list pay1 pay2))
      (values n1 n2
              (+ payoff1 (* (expt delta _) pay1))
              (+ payoff2 (* (expt delta _) pay2))
              (cons round-result round-results))))
 (values
   (reverse round-results)
   (if (zero? r1)
       (cons
        (automaton (hash-set head1 'PAYOFF (round5 pay1)) body1)
        i1)
       (cons
        o1
        (automaton (hash-set head1 'PAYOFF (round5 pay1)) body1)))
   (if (zero? r1)
       (cons
        o2
        (automaton (hash-set head2 'PAYOFF (round5 pay2)) body2))
       (cons
        (automaton (hash-set head2 'PAYOFF (round5 pay2)) body2)
        i2))
   ))

(define (interact* au1 au2 rounds delta)
  (with-handlers ([exn:fail?
                   (lambda (e) (values (list 'I-AM-HERE!!!) au1 au2))])
    (interact-d au1 au2 rounds delta)))

(define (interact-s s1 s2 rounds delta)
  (define-values (result a1 a2) (interact-d s1 s2 rounds delta))
  (round2 (hash-ref (automaton-head a1) 'PAYOFF)))

(define (interact-2 s1 s2 rounds delta)
  (define-values (result a1 a2) (interact-d s1 s2 rounds delta))
  (cons
   (round2 (hash-ref (automaton-head a1) 'PAYOFF))
   (round2 (hash-ref (automaton-head a2) 'PAYOFF))))


(define (round5 n)
  (/ (round (* 100000 n))
     100000))
(define (round2 n)
  (/ (round (* 100 n))
     100))

;; contest

(define (match-with* s lst)
  (for/list ([op lst])
    (interact-s s op 10 .9)))

(define (match-with ss lst)
  (for/list ([au ss])
    (match-with* au lst)))

(define (match-symmetric lst)
  (match-with lst lst))

(define (return-full lst)
  (for/list ([i lst])
    (for/list ([j lst])
      (interact-2 i j 10 .9))))

(define (transpose payoff)
  (apply map list payoff))

;; solve matrix form game

(define (findx v x)
  (for/list ([y v] [i (in-naturals)])
    (if (equal? x y) 'x '_)))

(define (br* possible-payoffs)
  (define max-possible (apply max possible-payoffs))
  (findx possible-payoffs max-possible))

(define (br payoff-table)
  (map br* (transpose payoff-table)))

(define (weave-br pay1 pay2)
  (define pay2t (transpose pay2))
  (map (lambda (l1 l2) (map list l1 l2))
       pay2t pay1))

(define (solve-symmetric-game lst)
  (define p1 (match-symmetric lst))
  (define br1 (br p1))
  (weave-br br1 br1))

;; personality test




;; EXPORT TO GRAPHVIZ

(define (scan-duplicate dispatch)
  (define destinations (hash-values dispatch))
  (if (apply equal? destinations)
      (list "\"D,H\"" "\"D,H\"")
      (list "\"D\"" "\"H\"")))

;; in dispatch, D is before H

(define (generate-dispatch-code state# dispatch)
  (define l (hash-count dispatch))
  (define ends (scan-duplicate dispatch))
  (remove-duplicates
   (for/list ([i l])
     (string-append
      (number->string state#)
      " -> "
      (number->string (hash-iterate-value dispatch i))
      " [ label = "
      (list-ref ends i)
      " ] \n"))))

(define (generate-dispatch-codes body)
(define state-ids (hash-keys body))
  (define dispatches (map state-dispatch (hash-values body)))
  (define dispatch-code
    (for/list ([i state-ids] [j dispatches])
      (generate-dispatch-code i j)))
  (apply string-append (flatten dispatch-code)))

(define (generate-state-code body)
  (define l (hash-count body))
  (define label-code
    (for/list ([i l])
      (string-append
       (number->string i)
       " [label = \""
       (symbol->string (state-action (hash-ref body i)))
       "\"] \n")))
  (apply string-append (flatten label-code)))

(define (generate-dot-code au name)
  (match-define (automaton head body) au)
  (string-append
   "digraph finite_state_machine {
            rankdir=LR
            size=\"8,5\"
            node [shape = doublecircle]; "
   (number->string (hash-ref head 'INITIAL))
   "
            node [shape = circle] \n \n"
   (generate-state-code body)
   "\n"
   (generate-dispatch-codes body)
   "
    labelloc=\"b\"
    label = \"" name  "\"
    } \n"))

(define (export-dot-code au au-name)
  (with-output-to-file "au.gv"
    (lambda () (printf (generate-dot-code au au-name)))
    #:exists 'append))

(define (export-dot-codes a-list name)
  (for ([i (length a-list)])
    (export-dot-code (list-ref a-list i)
                     (string-append (symbol->string name)
                                    (number->string i))
                     )))


(define (export-automata-in-dot cycle rankings)
  (for ([(key value) (in-hash rankings)])
    (and
     (> value 5)
     (export-dot-code key (string-append
                           (number->string cycle)
                           (number->string value))))))
