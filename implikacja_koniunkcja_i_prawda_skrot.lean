-- W maksymalnym skrócie (być może użytecznym na etapie powtarzania materiału):

-- Dowód koniunkcji to para uporządkowana dowodów jej członów.

-- (poniżej czytaj typowania jak zdania, na przykład, `1 : Nat` ↦ "`1` ma typ `Nat`", a fragmenty
-- zapisane jako `<charakterystyka termu>` jako miejsca, w których ma się pojawić term
-- scharakteryzowany w dany sposób)

-- Jeżeli `p : Prop` i `q : Prop`, to `(And.intro <dowód p> <dowód q>) : p ∧ q`.

-- Jeżeli `h : p ∧ q`, to `h.left : p` (równoważnie `(And.left h) : p`) i `h.right : q` (równoważnie
-- `(And.right h) : q`).

-- `True : Prop` i istnieje dokładnie jeden term tego typu ─ `True.intro`.

-- Reguły wiązań operatorów określają strukturę termów, które zostały zapisane z pominięciem
-- nawiasów. Ponieważ strzałka wiąże z prawej, Lean interpretuje  `p → q → r` jako `p → (q → r)`.
-- Ponieważ aplikacja wiąże z lewej, dla Leana `suma 1 2` to `(suma 1) 2`. W obydwu przypadkach
-- upraszcza się najczęstszy zapis.
