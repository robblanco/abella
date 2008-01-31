eval zero zero.
eval true true.
eval false false.
eval (succ M) (succ V) :- eval M V.
eval (pred M) zero :- eval M zero.
eval (pred M) V :- eval M (succ V).
eval (is_zero M) true :- eval M zero.
eval (is_zero M) false :- eval M (succ V).
eval (if M N1 N2) V :- eval M true, eval N1 V.
eval (if M N1 N2) V :- eval M false, eval N2 V.
eval (abs T R) (abs T R).
eval (app M N) V :- eval M (abs T R), eval (R N) V.
eval (rec T R) V :- eval (R (rec T R)) V.

of zero num.
of true bool.
of false bool.
of (succ M) num :- of M num.
of (pred M) num :- of M num.
of (is_zero M) bool :- of M num.
of (if M N1 N2) T :- of M bool, of N1 T, of N2 T.
of (abs T R) (arr T U) :- pi n\ (of n T => of (R n) U).
of (app M N) T :- of M (arr U T), of N U.
of (rec T R) T :- pi n\ (of n T => of (R n) T).
