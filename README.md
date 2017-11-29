# OCaml PLTP: An independent reproduction of the Boyer-Moore Pure Lisp Theorem Prover

A fully automatic inductive theorem prover for a logic based on Pure Lisp.
Modeled on the original Boyer-Moore prover presented in Moore's PhD, 1973.

# Why

The original Boyer-Moore Pure Lisp Theorem Prover is the "big bang" of the universe (multiverse!) of automated induction.

It's an incredible thrill to work through their original design and reproduce the proofs independently. J Moore's PhD thesis is written in a way that makes this possible. Sadly, many works in automated reasoning do not have this property. We should all strive to write more like J Moore and Bob Boyer.

PLTP represents many aspects of automated induction in their most essential form.
Studying PLTP is a great way to learn about simplification, induction schemes, generalisation, fertilisation, and the interplay between recursion and induction.

Did you know that PLTP could prove `(EQUAL (REV (REV x)) x)` fully automatically in 1973, without any lemmas? 

# How

From an OCaml toplevel, execute `#use "Pltp.ml";;`

Examples can be found at the end of `Pltp.ml`.

An example proof:

```
# prove(Equal(f_reverse(f_reverse(c_a)), c_a));;

Theorem to be proved:

(EQUAL (REVERSE (REVERSE A)) A)

Must try induction.

Induct on A.

The theorem to be proved is now:

(AND (EQUAL (REVERSE (REVERSE NIL)) NIL)
     (IMPLIES (EQUAL (REVERSE (REVERSE A)) A)
              (EQUAL (REVERSE (REVERSE (CONS A1 A))) (CONS A1 A))))

Evaluation yields:

(COND (COND (EQUAL (REVERSE (REVERSE A)) A)
            (COND (EQUAL (REVERSE (APPEND (REVERSE A) (CONS A1 NIL)))
                         (CONS A1 A))
                  T NIL)
            T)
      T NIL)

Normalizes to:

(COND (EQUAL (REVERSE (REVERSE A)) A)
      (EQUAL (REVERSE (APPEND (REVERSE A) (CONS A1 NIL))) (CONS A1 A))
      T)

Fertilize with (EQUAL (REVERSE (REVERSE A)) A).

The theorem to be proved is now:

(COND (EQUAL (REVERSE (APPEND (REVERSE A) (CONS A1 NIL)))
             (CONS A1 (REVERSE (REVERSE A))))
      T (*1))

Generalize common subterms by replacing (REVERSE A) by GENRL1.

The generalized term is:

(COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
             (CONS A1 (REVERSE GENRL1)))
      T (*1))

Must try induction.

Merged two faults into one.

Induct on GENRL1.

The theorem to be proved is now:

(AND (COND (EQUAL (REVERSE (APPEND NIL (CONS A1 NIL)))
                  (CONS A1 (REVERSE NIL)))
           T (*1))
     (IMPLIES (COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                           (CONS A1 (REVERSE GENRL1)))
                    T (*1))
              (COND (EQUAL (REVERSE (APPEND (CONS GENRL11 GENRL1)
                                            (CONS A1 NIL)))
                           (CONS A1 (REVERSE (CONS GENRL11 GENRL1))))
                    T (*1))))

Evaluation yields:

(COND (COND (COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                         (CONS A1 (REVERSE GENRL1)))
                  T (*1))
            (COND (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                                       (CONS GENRL11 NIL))
                               (CONS A1
                                     (APPEND (REVERSE GENRL1)
                                             (CONS GENRL11 NIL))))
                        T (*1))
                  T NIL)
            T)
      T NIL)

Normalizes to:

(COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
             (CONS A1 (REVERSE GENRL1)))
      (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                           (CONS GENRL11 NIL))
                   (CONS A1 (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
            T (*1))
      (COND (*1)
            (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                                 (CONS GENRL11 NIL))
                         (CONS A1
                               (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
                  T (*1))
            T))

Reduces to:

(COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
             (CONS A1 (REVERSE GENRL1)))
      (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                           (CONS GENRL11 NIL))
                   (CONS A1 (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
            T (*1))
      (COND (*1)
            (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                                 (CONS GENRL11 NIL))
                         (CONS A1
                               (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
                  T T)
            T))

Normalizes to:

(COND (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
             (CONS A1 (REVERSE GENRL1)))
      (COND (EQUAL (APPEND (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                           (CONS GENRL11 NIL))
                   (CONS A1 (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
            T (*1))
      T)

Fertilize with (EQUAL (REVERSE (APPEND GENRL1 (CONS A1 NIL)))
                      (CONS A1 (REVERSE GENRL1))).

The theorem to be proved is now:

(COND (COND (EQUAL (APPEND (CONS A1 (REVERSE GENRL1)) (CONS GENRL11 NIL))
                   (CONS A1 (APPEND (REVERSE GENRL1) (CONS GENRL11 NIL))))
            T (*1))
      T (*2))

Evaluation yields:

T

Q.E.D.
```

# References

* [Computational Logic: Structure Sharing and Proof of Program Properties, J S. Moore's PhD thesis, University of Edinburgh, 1973](http://www.cs.utexas.edu/users/moore/publications/Moore-Thesis-1973-OCR.pdf)

* [Proving Theorems about LISP Functions, R.S. Boyer and J S. Moore. Journal of the Association for Computing Machinery, 22(1), 1975, pp.129-144](http://www.cs.utexas.edu/users/moore/publications/bm75.pdf)


# Contact

Grant Passmore, Aesthetic Integration

grant@aestheticintegration.com

http://www.imandra.ai

http://www.cl.cam.ac.uk/~gp351
