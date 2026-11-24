-- To wyłącza ostrzeżenia o niewykorzystanych parametrach
set_option linter.unusedVariables false

-- Niech to będą jakieś zdania i jakieś predykaty dotyczące (bo czemu nie) liczb naturalnych
variable (p q r : Prop) (P Q R : Nat → Prop)

----------------------------------------------------------------------------------------------------
-- RACHUNEK ZDAŃ

example : p → p := by sorry

example : p ↔ p := by sorry

example : p ↔ p := ⟨sorry, sorry⟩

example : p → q → p ∧ q := sorry

example : p ∧ q → p := sorry

-- Częściowy dowód przemienności koniunkcji
example : p ∧ q → q ∧ p := sorry -- raz w trybie interaktywnym, a raz pisząc kod wprost

-- Ex contradictione quodlibet
example : p ∧ ¬p → q := sorry

-- Kontrapozycja
example : p → q → (¬q → ¬p) := sorry

example : q → p ∨ q := sorry

example : (p → r) → (q → r) → (p ∨ q → r) := sorry

-- Dowód implikacji w drugą stronę wymaga zastosowania aksjomatu wyłączonego środka (czyli logiki
-- klasycznej).
example : p ∨ q → ¬p → q := sorry

-- Dowód implikacji w drugą stronę wymaga zastosowania aksjomatu wyłączonego środka (czyli logiki
-- klasycznej).
example : p → ¬(¬p) := sorry

-- Rozdzielność dodawania względem mnożenia!
example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := sorry

-- A to jest odpowiednik rozdzielności mnożenia względem dodawania (?). Obie te rozdzielności można
-- wyrazić jako równoważności (`↔`).
example : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := sorry

-- Nasz zdaniowy final boss to prawa De Morgana (w których używamy wszystkich spójników):
example : ¬(p ∧ q) ↔ ¬p ∨ ¬q := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

----------------------------------------------------------------------------------------------------
-- RACHUNEK PREDYKATÓW

-- TODO
