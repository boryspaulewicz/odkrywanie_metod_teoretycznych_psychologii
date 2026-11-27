-- W maksymalnym skrócie (być może użytecznym na etapie powtarzania materiału):

-- `True : Prop` i istnieje dokładnie jeden term tego typu ─ `True.intro`. Ponieważ dowód zdania
-- `True` ma swoją globalnie dostępną nazwę, `True` wynika z każdego zdania:
example (p : Prop) : p → True := fun _ => True.intro -- `_`, bo nie używamy wartości parametru

-- Dowód koniunkcji to para uporządkowana dowodów jej członów.
example (p q : Prop) : p → q → p ∧ q := fun hp => fun hq => And.intro hp hq -- albo ⟨hp, hq⟩

-- Używamy koniunkcji wydobywając z niej dowód lewego lub prawego członu:
example (p q : Prop) : p ∧ q → p := fun h => And.left h -- albo `h.left`
example (p q : Prop) : p ∧ q → q := fun h => And.right h -- albo `h.right`
-- Można też tak, bo istnieje tylko jeden sposób skonstruowania dowodu koniunkcji:
example (p q : Prop) : p ∧ q → p := fun ⟨hp, _⟩ => hp
example (p q : Prop) : p ∧ q → q := fun ⟨_, hq⟩ => hq

-- Reguły *wiązań operatorów* określają strukturę termów, które zostały zapisane z pominięciem
-- nawiasów. Ponieważ strzałka wiąże z prawej, Lean interpretuje  `p → q → r` jako `p → (q → r)`.
-- Ponieważ aplikacja wiąże z lewej, `suma 1 2` to `(suma 1) 2`. W obydwu przypadkach upraszcza się
-- najczęstszy zapis.
