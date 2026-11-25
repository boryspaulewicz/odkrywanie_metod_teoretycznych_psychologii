-- To wyłącza ostrzeżenia o niewykorzystanych parametrach:
set_option linter.unusedVariables false

-- Niech to będą jakieś zdania i jakieś predykaty dotyczące liczb naturalnych (bo czemu nie):
variable (p q r : Prop) (P Q R : Nat → Prop)

-- Na początek (być może irytująca) ciekawostka:
theorem idProp0 : (p : Prop) → p → p := fun p : Prop => fun hp : p => hp
theorem idProp1 (p : Prop) : p → p := fun hp : p => hp
theorem idProp2 (p : Prop) (hp : p) : p := hp
theorem idProp3 : ∀ p : Prop, p → p := fun p : Prop => fun hp : p => hp
theorem idProp4 : ∀ p : Prop, ∀ hp : p, p := fun p : Prop => fun hp : p => hp
example : (idProp0 = idProp1) ∧ (idProp1 = idProp2) ∧ (idProp2 = idProp3) ∧ (idProp3 = idProp4)
   := ⟨by rfl, ⟨by rfl, ⟨by rfl, by rfl⟩⟩⟩

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

-- Jak udowodnisz `some_theo`, ten przykład zacznie naprawdę działać:
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
  -- Aplikacja aksjomatu parametrycznego `em` do zdania `p` jest dowodem `p ∨ ¬p`. Żeby skorzystać z
  -- dowodu alternatywy do udowodnienia jakiegoś zdania `r` (tutaj akurat chodzi o `p ∨ q`), trzeba
  -- wykazać, że `r` wynika zarówno z *samego* lewego *jak i* z *samego* prawego członu:
  apply (em p).elim
  -- Jeżeli chcemy zastosować (`apply`) do zrealizowania celu regułę eliminacji alternatywy dla
  -- *tej* alternatywy, czyli jeżeli chcemy w tym momencie zastosować w jakiś sposób dowód
  -- implikacji `(p ∨ ¬p) → (p → r) → (¬p → r) → r`, to ─ czego Lean się domyśla ─ `r`-em musi być
  -- `p ∨ q`, a my musimy dostarczyć dowody implikacji `p → p ∨ q` (to będzie łatwe) i `¬p → p ∨ q`.
  apply Or.inl -- `Or.inl` (po odgadnięciu implicitnych parametrów) to w tym momencie dosłownie cały
  -- aktualny cel, a więc zostaje nam tylko do zrobienia dowód `¬p → p ∨ q`:
  intro np
  -- Ponieważ mamy `h : ¬p → q` i `np : ¬p`, to teraz wystarczy ...
  apply Or.inr
  sorry

-- (Nawiasem mówiąc, uogólnienie używanej przez nas do tej pory logiki konstruktywnej do logiki
-- *klasycznej* sprowadza się do dopuszczenia możliwości korzystania z aksjomatu `em`)

-- Również w tym przypadku dowód implikacji w drugą stronę wymaga zastosowania aksjomatu wyłączonego
-- środka (czyli logiki klasycznej).
example : p → ¬(¬p) := sorry

-- Rozdzielność dodawania względem mnożenia!
example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := sorry

-- A to jest odpowiednik rozdzielności mnożenia względem dodawania (?). Obie te rozdzielności można
-- wyrazić jako równoważności (`↔`).
example : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := sorry

-- Akurat ta strzałka jest "szalenie kanoniczna" (o czym może kiedy indziej):
example : p ∧ q → p ∨ q := sorry

-- Nasz zdaniowy final boss to prawa De Morgana (w których używamy wszystkich spójników):
example : ¬(p ∧ q) ↔ ¬p ∨ ¬q := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

----------------------------------------------------------------------------------------------------
-- RACHUNEK PREDYKATÓW

-- To jest (znacznie) prostsze niż (być może początkowo) myślisz!
example : ∀ n : Nat, P n → P n := fun n => sorry

example : ∀ n : Nat, P n ∧ Q n → P n := sorry

example : ∀ n : Nat, P n → P n ∨ Q n := sorry

example : ∀ n : Nat, P n ∧ Q n → Q n := sorry

example : ∀ n : Nat, P n ∧ Q n → Q n ∧ P n := sorry

example : ∀ n : Nat, P n ∨ Q n → Q n ∨ P n := sorry

example : ∀ n : Nat, P n ∧ ¬(P n) → Q n := sorry

example : ∀ n : Nat, (P n → Q n) → ¬(Q n) → ¬(P n) := sorry

example : ∀ n : Nat, ¬(P n ∧ Q n) → ¬(P n) ∨ ¬(Q n) := sorry

example : ∀ n : Nat, ¬(P n ∨ Q n) → ¬(P n) ∧ ¬(Q n) := sorry

-- Dopiero od tego momentu kwantyfikatory "coś wnoszą" do dowodów. Już wiesz, czemu wcześniej duży
-- kwantyfikator i struktura podmiot-orzeczenie nie miały właściwie znaczenia?

-- To tak nie działa z alternatywą. Domyślasz się czemu?
example : (∀ n : Nat, P n ∧ Q n) → (∀ n : Nat, P n) ∧ (∀ n : Nat, Q n) := sorry

example : (∃ n : Nat, P n ∧ Q n) → (∃ n : Nat, P n) ∧ (∃ n : Nat, Q n) := sorry

example : (∀ n : Nat, ¬(P n)) → ¬(∃ n : Nat, P n) := sorry

example : ¬(∃ n : Nat, P n) → (∀ n : Nat, ¬(P n)) := sorry

-- Dowód implikacji w drugą stronę wymaga logiki klasycznej, czyli na przykład aksjomatu `em`:
example : (∃ n : Nat, ¬(P n)) → ¬(∀ n : Nat, P n) := sorry
