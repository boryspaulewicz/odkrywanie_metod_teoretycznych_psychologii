----------------------------------------------------------------------------------------------------
-- PARAMETRYZOWANIE = UZMIENNIANIE = ABSTRAHOWANIE = "FUNKCJONOWANIE"

-- Poniżej widzimy kilka przykładów *tego samego* sprawdzania "zgadzania się" typu i termu,
-- *zapisane* na 7 (powierzchownie) różnych sposobów. Zwróć uwagę, że położenie głównego dwukropka,
-- to jest tego, który oddziela listę parametrów od specyfikacji typu rezultatu, jest kwestią wyboru
-- (albo "gustu"). *Jedyny* warunek jest taki, żeby coś było po prawej od tego dwukropka ─ inaczej
-- powstałoby dziwne `cośtam : :=`, a poza tym to by nie była funkcja.

example (m : Nat) (n : Nat) : Nat := m + n
example (m n : Nat) : Nat := m + n -- tak też można, bo oba parametry mają ten sam typ
example (m : Nat) : Nat → Nat := fun n : Nat => m + n
example : Nat → Nat → Nat := fun m : Nat => fun n : Nat => m + n
-- Widzisz wzorzec w dotychczasowych przykładach? Parametry funkcji można "obsłużyć" albo po lewej,
-- albo po prawej od głównego dwukropka, wybór należy do Ciebie.
example : Nat → Nat → Nat := by -- `by` := wejdź w tryb interaktywny (czyli prowadź mnie za rączkę)
  -- Zrób `fun m => (fun n => ...)`, czyli potraktuj `m` i `n` jako parametry=zmienne=termy
  -- hipotetyczne=założenia ...
  intro m n
  -- ... i dodaj do konstrukcji dokładnie/wprost ten term:
  exact m + n
example (m : Nat) : Nat → Nat := by
  -- Tutaj `m` już jest parametrem, a więc jest od razu widoczne w trybie interaktywnym, bo
  -- podaliśmy specyfikację tego parametru przed głównym dwukropkiem
  intro n
  exact m + n
example (m n : Nat) : Nat := by
  -- Tutaj `m` i `n` są już parametrami
  exact m + n
-- To wszystko są różne sposoby zapisania tego samego termu (o tym samym typie <z konieczności, bo
-- typy termów są unikalne>). Ponieważ twierdzenia to funkcje, przesuwalność głównego dwukropka
-- działa dla twierdzeń tak samo (to jest to samo zdanie i ten sam dowód, tylko inaczej zapisane):
example : (p : Prop) → p → p := fun _ => fun hp => hp
example (p : Prop) : p → p := fun hp => hp
example (p : Prop) (hp : p) : p := hp
-- Nawet tak można (bo Lean potrafi się tu domyślić typu rezultatu, o czym za chwilę), chociaż to
-- "brzydki" styl:
def idProp (p : Prop) (hp : p) := hp
#check @idProp -- idProp : ∀ (p : Prop), p → p

/-
Wracając do trybu interaktywnego, czy widzisz, że `intro m` (odpowiadające dokładnie `fun m =>`)
znaczy tyle, co "potraktuj `m` *abstrakcyjnie*", to jest jako *jakieś* coś (danego typu), albo
"*abstrahuj od* `m`"", a to znaczy to samo, co "potraktuj `m` jako *parametr/zmienną*", a to znaczy
to samo, co "potraktuj `m` jako *wejście jakiejś funkcji*"?

*Abstrahowanie = parametryzowanie = uzmiennianie = robienie z czegoś funkcji czegoś*!

W szczególności, ...
-/

example (m n : Nat) : Nat := m + n

/-
.. odpowiada wiernie temu, co matematycy mają na myśli, zaczynając wypowiedź od ...

"Niech `m` i `n` będą liczbami naturalnymi. Wtedy `m + n` jest liczbą naturalną, która ..."

... albo ...

"Dla liczb naturalnych `m` i `n`, `m + n` to liczba naturalna, która ...".

I oba te *fragmenty tekstu* są de facto pewnymi *funkcjami*!

A my, *psychologowie*? Kiedy na przykład piszemy, że zgodnie z taką a taką teorią, "jeżeli bodziec
`s2` następuje w każdej próbie po bodźcu `s1`, to ...", *musimy* mieć na myśli `s1` i `s2` jako
*zmienne*, których wartość czy treść zależy od *konkretnego zastosowania* takiego czy innego
*schematu badawczego*. Dlatego każdy schemat badawczy jest de facto *funkcją*. Jak każda funkcja,
schemat (albo "paradygmat") badawczy ma zawsze jakieś parametry *określonego typu*, które jednak
wtedy nazywamy raczej *warunkami stosowalności*. Widzisz, że na pewnym poziomie ogólności nie ma tu
zasadniczej różnicy? Z drugiej strony, na pewnym poziomie ogólności można powiedzieć (że) wszystko
(jest) jedno co(ś).

Deklaracja `variable` mówi tak naprawdę: Hej, Lean, użyj tego jako parametru (czyli zmiennej) *tam*,
gdzie `m` pojawi się *"znienacka"* . Czyli `variable (m : Nat)` można odczytać jako "jakby co, to
`m` ma być zmienną typu `Nat`". Matematycy (i psychologowie) często stosują takie skrótowe sposoby
mówienia, polegające na pominięciu wcześniejszych jawnych deklaracji typów zmiennych, na przykład
(najpierw matematycy), ...

"Suma liczb naturalnych `m` i `n` jest ..."

... albo (a teraz psychologowie):

"Randomizacja klasy bodźca `S` sprawia, że korelacja między `S` i `RT` jest ..."
-/

variable (m : Nat)

/-
Ponieważ Lean domyśla się w ten sposób, co ma być zmienną, to chociaż to, co jest napisane poniżej
przed `:=`, nie *wygląda* na pierwszy rzut oka jak początek definicji funkcji, skoro używamy tu
symbolu `m` bez dodatkowych wyjaśnień (czyli znienacka), Lean traktuje to jako `parametr` (czyli
zmienną, czyli ...), ...
-/

def nast := m + 1
-- Lean musi tu rozstrzygnąć, czym ma być to `m`. A więc szuka informacji wyżej, i w tym wypadku
-- znajduje (nasze) wyjaśnienie (w postaci globalnej deklaracji `variable`).

-- ... wobec czego Lean musi potraktować definicję `nast` jako definicję *funkcji*. Tak też robi
-- (automatycznie uzupełniając parametryzację):

#check nast  -- nast (m : Nat) : Nat
#check @nast -- nast : Nat → Nat

def dodaje (n : Nat) := m + n -- Domyślasz się, jak Lean potraktuje tą definicję?
#check dodaje                 -- Zadanie1: Zgadnij, co się tu pojawi.

/-
Zamiast, tak jak to robiliśmy wcześniej, deklarować *globalnie* za pomocą `variable`, że na przykład
`p` i `q` to (domyślnie, bo możemy to lokalnie zmienić) jakieś zdania, możemy wykorzystać miejsce po
słowie kluczowym `example`, a przed głównym dwukropkiem, do *lokalnej* deklaracji zmiennych, których
w danym miejscu używamy (lokalne deklaracje przesłaniają deklaracje globalne tych samych symboli):
-/

example (p q : Prop) : (p ∧ ¬p) → q := fun h => False.elim (h.right h.left)

#check p
-- Lean sygnalizuje błąd, bo `p` nie ma ani widocznej *stąd*, to jest *globalnie*, deklaracji, ani
-- widocznej stąd definicji.

/-
To ostatnie `example` czytamy: Niech `p` i `q` będą zdaniami. Wtedy (`:`) typ `(p ∧ ¬p) → q` ma
między innymi (`:=`) term `fun h => False.elim (h.right h.left)`. Czy widzisz, że gdyby nie
wcześniejsza deklaracja `(p q : Prop)`, to wyrażenie `(p ∧ ¬p) → q` *nie miałoby sensu*? No bo skąd
Lean miałby wiedzieć, czym mają być `p` i `q`?

(Właściwie mógłby się domyślić, o co chodzi, na podstawie samego użycia operacji "koniunkcjowania"
`∧`, ale nie ma takiej wbudowanej domyślności.)

Ponadto, gdyby nie nawiasy w `False.elim (h.right h.left)`, Lean pomyślałby, że chodzi o aplikację
`False.elim` do *dwóch* argumentów. Ponieważ *aplikacja* `h.right h.left` ma typ `False`, to można
było też równoważnie napisać `(h.right h.left).elim`, czyli wywołać na rzecz (<hipotetycznego>
rezultatu) tej aplikacji składową `.elim` w ten sposób. To tylko inny sposób zapisania tej samej
operacji. Lean pozwala na taką swobodę dla naszej wygody.

A to jest definicja funkcji `dodaje1`, ale tym razem zapisana z jawnym typem rezultatu `: Nat`
(zaraz przed `:=`):
-/

def dodaje1 (n : Nat) : Nat := n + 1

/-
Zwracam tym razem Twoją uwagę na to, że główny dwukropek *bywa opcjonalny* (gdy Lean może się
domyślić, o co chodzi). Wcześniej, gdy definiowałem funkcję `dodaje1`, nie podałem jawnie typu
rezultatu (pisałem tylko `def dodaje1 (n : Nat) := n + 1`), bo suma dwóch liczb naturalnych musi być
liczbą naturalną, więc nie musiałem go podawać. `(n : Nat) : Nat` to zatem *pełna* specyfikacja typu
stałej `dodaje1`, określająca typ parametru i ─ po głównym dwukropku ─ typ rezultatu. Tą samą
konwencję zastosujemy niebawem.

(Nawiasem mówiąc, w razie wątpliwości lepiej nie używać skrótów.)

Gdy stosujemy tego rodzaju zapis definicji funkcji, po lewej od głównego dwukropka mamy widoczne "ze
środka" definiowanego "pudełka" (funkcji) nazwy (tutaj tylko `n`) i typy (`Nat`) "otworów
wejściowych", a po prawej od głównego dwukropka mamy tylko typ "otworu wyjściowego" (czyli rezultatu
zastosowania funkcji), już *bez* (zmiennej) *nazwy*. Nadawanie *wyjściu* funkcji nazwy nie ma sensu,
bo rezultatem działania funkcji jest to, co "oblicza" albo "robi" jej *całe* ciało (tutaj `n + 1`).
Równoważnie, można było zapisać to tak (nazwa to teraz `dodaje1'` z apostrofem, bo `dodaje1` już
wcześniej, hm, stało się *stałą*):
-/

def dodaje1' : Nat → Nat := fun (n : Nat) => n + 1

/-
Czytamy to: definiuję (`def`) stałą `dodaje1'` typu (`:`) `Nat → Nat` jako (`:=`) funkcję, która
przekształca `n : Nat` w `n + 1`.

Czyli typowa całkiem "oficjalna" albo całkiem eksplicitna definicja funkcji, taka jakby stojąca w
niedzielę rano przed chałupą w wykrochmalonej koszuli, wygląda następująco:

`def` <nazwa stałej> <specyfikacja parametru>+ `:` <typ rezultatu> `:=` <ciało funkcji>

gdzie <cośtam>+ znaczy <cośtam> występujące raz lub więcej razy.

(Nawiasem mówiąc, czy widzisz, że potoczne "*nast*ępująco" znaczy mniej więcej to samo, co "jak
podano na pozycji <albo w *kroku*> + 1"?)
-/

----------------------------------------------------------------------------------------------------
-- TWIERDZENIA TO TAKIE "DEFINITYWNE" STWIERDZENIA

-- To również *definicja funkcji*, tylko zapisana za pomocą słowa kluczowego `theorem`, żeby Lean
-- traktował ją tak, jak "lubi" traktować udowodnione twierdzenia. A lubi je traktować jako
-- *funkcje, których aplikacji się nie ewaluuje* (tylko sprawdza się ich typ).

theorem ecq {p q : Prop} (h : (p ∧ ¬p)) : q := (h.right h.left).elim

/-
Nazwa `ecq` to skrót od "ex contradictione quodlibet", czyli "ze sprzeczności wynika wszystko" (ta
zasada obowiązuje m.in. w logikach konstruktywnej i klasycznej, ale już w parakonsystentnych nie).

(Nawiasem mówiąc, pierwsze zdanie arykułu Wikipedii poświęconego hasłu "logika parakonsystentna"
określa <każdą> taką logikę jako "dopuszczającą wystąpienie sprzeczności, pod warunkiem, że nie
prowadzi do przepełnienia systemu". "Przepełnienia systemu"! Czy widzisz tu pewien trudny do
wyrażenia wprost związek z tym, że ludzie czasami tolerują niektóre sprzeczności czy niespójności, a
nawet bywa i tak, że z nich chętnie korzystają, i wtedy nazywają je *paradoksami*, ale zdarzają się
też sprzeczności czy niespójności, takie jak niektóre wyraźne *niekonsekwencje* w zachowaniach,
których ludzie <gdy te są widoczne!> nie są za bardzo w stanie tolerować?)

Specyfikacja parametrów `p` i `q` jest tutaj *implicitna* inaczej *niejawna*, co poznajemy po
nawiasach *klamrowych*. Wyrażenie `{p q : Prop}` czytamy jako "Hej, Lean, domyślaj się, czym mają
być `p` i `q`, z kontekstu użycia tej funkcji". Dzięki temu Lean domyśli się, *gdy będzie umiał*,
wartości tych parametrów i wtedy nie będziemy musieli podawać ich *wartości* (czyli odpowiadających
im *argumentów aplikacji*) jawnie, co zwiększy czytelność i zwięzłość zapisu.

To dobry przykład wykorzystania parametryzacji implicitnej:
-/

def uogólniona_identyczność {typ : Type} (parametr : typ) := parametr

-- Lean wywnioskował, że musi tu chodzić o `uogólniona_identyczność Nat 1`, bo term `1` ma typ
-- `Nat`:
#eval uogólniona_identyczność 1 -- `1`
-- A tu wywnioskował, że chodzi o typ `String`:
#eval uogólniona_identyczność "1" -- `"1"`

/-
Wróćmy do definicji `ecq`. Czy mimo zapisu `(h : (p ∧ ¬p)) : q` widzisz już, że chodzi o twierdzenie
`(p ∧ ¬p) → q`? W końcu ta funkcja-twierdzenie przekształca coś (dowód) typu (zdania) `p ∧ ¬p` w coś
(dowód) typu (zdania) `q`.

Czytamy to: My (pluralis maiestatis), szanowne twierdzenie `ecq`, *dla każdego* zdania `p` i `q` (to
tutaj *zmienne* <i zarazem ⟦niejawne⟧ parametry>) ─ których Lean spróbuje się sam domyślić z
kontekstu, w którym Nas zastosujesz ─ jeżeli dasz Nam jakiś dowód zdania `p ∧ ¬p`, dostarczymy ci
dowód zdania `q`.
-/

-- *To samo* można zapisać tak ...
example (r s : Prop) (h : r ∧ ¬r) : s := ecq h        -- lub tak, ...
example (r s : Prop) : (r ∧ ¬r) → s := fun h => ecq h -- ... lub tak,
-- ... a nawet tak (prowokując *ostrzeżenia o stylu*):
example : (r s : Prop) → (r ∧ ¬r) → s := fun r => fun s => fun h => ecq h
-- Możemy się pozbyć tych ostrzeżeń używając `_`, ...
example : (r s : Prop) → (r ∧ ¬r) → s := fun _ => fun _ => fun h => ecq h
-- ... ale zostawię resztę, bo mi się podoba, jak migocą.
example : (r s : Prop) → (r ∧ ¬r) → s := fun (r : Prop) => fun (s : Prop) => fun h => ecq h
example : (r s : Prop) → (r ∧ ¬r) → s := (fun (r : Prop) => (fun (s : Prop) => (fun h => ecq h)))
example : (r : Prop) → (s : Prop) → (r ∧ ¬r) → s := fun (r : Prop) => fun (s : Prop) => fun h => ecq h

/-
Skupmy się chwilowo (czy w ogóle można się skupić trwale? Czy skupianie <się> nie jest *stałym*
*przekierowywaniem*, a nie kierowaniem, "energii mentalnej" będącej *zawsze* w ruchu? <Tego
rodzaju rozważania zwykle poprzedzają formalizację ⟦a to była spora dystrakcja!⟧>) na tej wersji:
-/

example (r s : Prop) : (r ∧ ¬r) → s := fun h => ecq h

/-
Co się tutaj stało? Lean domyślił się, że parametr funkcji anonimowej `h` musi mieć typ `r ∧ ¬r`,
dlatego nie musieliśmy jawnie podawać typu `h`. W ciele tej funkcji *stosujemy* udowodnione
wcześniej *twierdzenie* `ecq`, bo u nas (a tak naprawdę to nie tylko u nas, tylko w ogóle zawsze i
wszędzie) *twierdzenia to programy zwracające dowody zdań*. To twierdzenie wymaga tylko jednego
*jawnego* argumentu, to jest dowodu *jakiejkolwiek* sprzeczności. *Jakiejkolwiek*, bo to, jakie
zdanie występuje w tej sprzeczności, jest (niejawnym ...) *parametrem* twierdzenia `ecq` (... dzięki
czemu Lean się tego sam domyśla, a my mamy krótszy kod). Teraz zrobimy to samo w trybie
interaktywnym.
-/

-- Przejdź przez ten kod linia po linii, patrząc, jak zmienia się stan taktyczny po prawej.
example (r s : Prop) : (r ∧ ¬r) → s := by
  -- Słowo kluczowe `by` sprawia, że wchodzimy do *interaktywnego* trybu konstruowania termów
  -- (*dowolnych* termów, nie tylko dowodów!), w którym Lean próbuje nam pomóc, pokazując, czym już
  -- w danym miejscu definicji *lokalnie* dysponujemy i co mamy jeszcze do zrobienia.
  --
  -- W tym miejscu konstrukcji mamy do zrealizowania `1 goal`, którym jest `r ∧ ¬r → s`. To jest
  -- (docelowy) *typ* konstrukcji, którą mamy w danym miejscu w kodzie stworzyć, w trybie
  -- interaktywnym podany zawsze po symbolu derywacji `⊢`.
  --
  -- Jedyne parametry/zmienne, którymi w tym momencie dysponujemy, to *jakieś* zdania `r` i `s`, a
  -- także nie interesująca nas akurat teraz, "zabłąkana" (globalna) zmienna/parametr `m : Nat`. Czy
  -- już widzisz, że nad symbolem `⊢` mamy same parametry/zmienne (jak również ─ jak się przekonasz
  -- później ─ konstrukcje zrobione ze zmiennych)? A więc w trybie interaktywnym tak jakby "tworzymy
  -- od środka pudełko/mechanizm określonego rodzaju".
  intro h
  -- Gdy cel ma postać implikacji, a nasz cel przed chwilą miał właśnie taką postać, *taktyka*
  -- (taktyki działają tylko w trybie interaktywnym) `intro h` pozwala przyjąć założenie (=
  -- wprowadzić parametr/zmienną o typie zdaniowym), że "mamy" dowód poprzednika implikacji będącej
  -- aktualnym celem, i nazwać to założenie (czyli hipotetyczny dowód) literą `h`. Można też
  -- powiedzieć, że `intro h` tworzy sam początek kodu funkcji anonimowej `fun h =>`. Dla nas to
  -- przecież na jedno wychodzi. Dlatego po zastosowaniu tej taktyki, poprzednik celu-implikacji
  -- zostaje "oderwany" i "wskakuje" powyżej `⊢` jako coś, co odtąd "mamy" jako (zmienne, bo o
  -- *wartości zależnej od kontekstu aplikacji*) wejście.
  exact ecq h
  -- Ponieważ jesteśmy w trybie interaktywnym, nie możemy pisać kodu wprost i zamiast tego musimy
  -- używać do wszystkiego jakiś taktyk. Tutaj akurat użyliśmy taktyki `exact`, która wprowadza do
  -- definicji podany jako argument kod wprost. Lean mówi nam w tym momencie `No goals`, co znaczy,
  -- że skonstruowaliśmy poprawny dowód.

-- Proponuję chociaż raz spokojnie przejść również ten kod kursorem (cursor to łacińskie słowo
-- oznaczające biegacza), linia po linii, czytając przy tym komentarze, oglądając zmiany stanu
-- taktycznego i czasami trochę o tym wszystkim myśląc:
example (p q : Prop) : (p ∧ q) → (q ∧ p) := by
  intro hpandq -- lokalne założenia nazywamy niemal jak chcemy
  apply And.intro
  -- Czytamy to: Do stworzenia termu typu będącego aktualnym celem chcę zastosować (`apply`), ale
  -- *nie widząc jeszcze, skąd wezmę brakujące "składniki"*, term (będący zarazem funkcją i
  -- konstruktorem typu zdaniowego o postaci koniunkcji) `And.intro`.
  --
  -- Lean stąd automatycznie wnioskuje, że musimy mu dostarczyć dwa termy ─ jeden typu `q` (czyli
  -- dowód zdania `q`) i jeden typu `p`, bo tego wymaga w tym momencie osiągnięcie celu za pomocą
  -- `And.intro`, dlatego podaje te typy jako *dwa* cele.
  exact hpandq.right -- ten term "spełnia" pierwszy cel, ...
  exact hpandq.left  -- ... a ten drugi.

example (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro h
  intro nq
  -- Taktyka `unfold` *rozwija* podane z nazwy *definicje* w celu. Akurat tutaj chodzi o definicję
  -- negacji, która w Leanie nosi nazwę `Not`. Tą nazwę można było samodzielnie odkryć, umieszczając
  -- kursor nad symbolem negacji w kodzie (nie w komentarzu).
  unfold Not       -- po rozwinięciu definicji widać, że celem jest de facto implikacja (do fałszu)
  unfold Not at nq -- `at` pozwala stosować taktyki do termów/parametrów/zmiennych "na górze"
  intro hp
  -- A teraz widać, że mamy już tylko uzyskać term typu `False`, i od razu też widać, skąd *musimy*
  -- go ostatecznie wziąć ─ *korzystając* w *jakiś* sposób z `nq`, a więc możemy (m.in.) użyć tu
  -- `apply`:
  apply nq
  -- Lean sam wywnioskował, że aby to zrobić, musimy dostarczyć dowód/term typu `q`, bo inaczej `nq`
  -- tutaj nie "zadziała". Dlatego teraz celem jest `q`. Można to zrobić tak, ...
  --
  -- exact h hp
  --
  -- ... ale można też zrobić to bardziej leniwie i bezmyślnie:
  apply h
  exact hp

-- Zadanie 2: Czy jesteś w stanie dokończyć dowód twierdzenie o kontrapozycji `cp` (to skrót od
-- "contraposition"), korzystając z twierdzenia `ecq`?
theorem cp {p q : Prop} (h : p → q) : (¬q → ¬p) := by
  -- Termy `p : Prop`, `q : Prop` i `h : p → q` są tu od razu dostępne w trybie interaktywnym jako
  -- coś, co "mamy" ("na górze"), bo potraktowaliśmy je jako parametry tego twierdzenia
  -- (równoważnie: bo są przed głównym dwukropkiem).
  intro nq hp
  -- Używając w trybie interaktywnym taktyki `have`, możemy dodać do tego, co "mamy", nazwane termy,
  -- które jesteśmy w stanie w danym momencie skonstruować.
  have hc := And.intro (h hp) nq
  -- Term `hc` ma typ `q ∧ ¬q`, czyli to jest (też hipotetyczny, bo przecież został zrobiony z
  -- termów będących zmiennymi) dowód tej sprzeczności.
  exact ecq sorry

-- Wiesz już, co się poniżej dzieje?
example (p : Prop) : ¬p → ¬p := fun np : ¬p => np
example (p : Prop) : ¬p → ¬p := cp (fun hp : p => hp)
-- A domyślasz się, czemu poniżej po głównym dwukropku nie mogłem napisać `Prop → ¬p → ¬p`? Gdybym
-- tak zrobił, symbol `p` nie miałby określonego typu i Lean nie miałby pojęcia, o czym do niego
-- mówię.
example : (p : Prop) → ¬p → ¬p := fun _ => cp (fun hp => hp)
