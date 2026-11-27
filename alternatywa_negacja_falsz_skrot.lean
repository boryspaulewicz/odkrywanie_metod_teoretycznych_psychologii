-- Alternatywa, negacja i fałsz w skrócie (do powtarzania generatywnego)

#check False -- False : Prop

-- Fałsz to z definicji zdanie, które *nie ma dowodu*. A skoro tak, to dla każdego zdania `p`, można
-- skonstruować funkcję, która z każdego dowodu `False` zrobi dowód `p`, po prostu dlatego, że nie
-- ma z czego. Żeby skorzystać z tego faktu używamy reguły eliminacji dla (czysto hipotetycznych)
-- termów typu `False`:
example (p : Prop) : False → p := fun h => False.elim h -- albo `h.elim`

-- Dla każdego `p : Prop`, `¬p` to z definicji `p → False`. Dlatego ze sprzeczności wynika każde
-- zdanie:
example (p q : Prop) : (p ∧ ¬p) → q := fun ⟨hp, np⟩ => (np hp).elim -- albo `False.elim (np hp)`

-- Dowód alternatywy to *albo* dowód jej lewego członu, *albo* prawego. Konstruktory (to takie
-- funkcje *tworzące* termy określonego typu) lewego i prawego członu to odpowiednio `Or.inl` i
-- `Or.inr`
example (p q : Prop) : p → p ∨ q := fun hp => Or.inl hp
example (p q : Prop) : q → p ∨ q := fun hq => Or.inr hq

-- Żeby alternatywę do udowodnienia jakiegoś zdania, trzeba wykazać, że to zdanie wynika (w danym
-- kontekście!) zarówno z samego jej lewego członu jak i z samego prawego członu (i skorzystać z
-- funkcji `Or.elim`):
example (p q r : Prop) : (p → r) → (q → r) → p ∨ q → r :=
  fun hpr => fun hqr => fun hor => Or.elim hor hpr hqr -- albo `hor.elim hpr hqr`
