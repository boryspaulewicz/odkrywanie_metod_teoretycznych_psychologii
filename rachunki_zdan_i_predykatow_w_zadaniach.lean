-- To wyłącza ostrzeżenia o niewykorzystanych parametrach:
set_option linter.unusedVariables false

-- Niech to będą jakieś zdania i jakieś predykaty dotyczące liczb naturalnych (bo czemu nie):
variable (p q r : Prop) (P Q R : Nat → Prop)

----------------------------------------------------------------------------------------------------
-- RACHUNEK ZDAŃ

example : p → p := by sorry

example : p ↔ p := by sorry

example : p ↔ p := ⟨by sorry, sorry⟩

example : p → q → p ∧ q := sorry

example : p ∧ q → p := sorry

-- Częściowy dowód przemienności koniunkcji:
theorem some_theo : p ∧ q → q ∧ p := sorry
   -- może raz w trybie interaktywnym, a raz pisząc kod wprost?

-- Jak udowodnisz `some_theo`, ten przykład zacznie (sam) naprawdę działać:
example : (p ∧ q) ↔ (q ∧ p) := ⟨some_theo p q, some_theo q p⟩

-- Ex contradictione quodlibet:
example : p ∧ ¬p → q := sorry

-- Kontrapozycja:
example : p → q → (¬q → ¬p) := sorry

example : q → p ∨ q := sorry

example : (p → r) → (q → r) → (p ∨ q → r) := sorry

-- Dowód implikacji w drugą stronę wymaga zastosowania aksjomatu wyłączonego środka (czyli logiki
-- klasycznej).
example : p ∨ q → ¬p → q := sorry

-- Jeśli masz ochotę spróbować, to będziesz potrzebować czegoś takiego (`em` to skrót od "excluded
-- middle"):
axiom em (p : Prop) : p ∨ ¬p

-- Można to zrobić na wiele innych sposobów, w tym również (znacznie) krócej:
example : (¬p → q) → p ∨ q := fun h => by
  apply (em p).elim -- = `(p → r) → (¬p → r) → p ∨ ¬p → r`, gdzie `r` to `p ∨ q`
  apply Or.inl
  intro np
  apply Or.inr
  sorry

-- (Nawiasem mówiąc, do tego sprowadza się uogólnienie używanej przez nas do tej pory logiki
-- konstruktywnej do logiki klasycznej)

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
