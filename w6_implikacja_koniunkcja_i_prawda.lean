-- W maksymalnym skrócie (być może użytecznym na etapie powtarzania materiału):

-- Dowód koniunkcji to para uporządkowana dowodów jej członów. Jeżeli `p : Prop` i `q : Prop`, to
-- aplikacja `(And.intro <dowód p> <dowód q>) : p ∧ q`. Jeżeli `h : p ∧ q`, to `h.left : p` i
-- `h.right : q`.

-- `True : Prop` i istnieje dokładnie jeden dowód tego zdania ─ `True.intro`.

-- Currying: Każda funkcja dwuargumentowa to W Leanie tak naprawdę funkcja jednoargumentowa, która
-- zwraca funkcję jednoargumentową. Aplikacja funkcji dwuargumentowej do *jednego* argumentu zwraca
-- tą "wewnętrzną" funkcję. Funkcje n-argumentowe, gdzie n > 2, mają analogiczną strukturę i sposób
-- działania.

-- Reguły wiązań operatorów określają strukturę termów, które zostały zapisane z pominięciem
-- nawiasów. Ponieważ strzałka wiąże z prawej, Lean interpretuje  `p → q → r` jako `p → (q → r)`.
-- Ponieważ aplikacja wiąże z lewej, dla Leana `suma 1 2` to `(suma 1) 2`.

----------------------------------------------------------------------------------------------------
-- IMPLIKACJA, KONIUNKCJA, PRAWDA, CURRYING I WIĄZANIA OPERATORÓW

variable (p q r : Prop)

-- W pierwszej chwili może to się wydawać dziwne, ale `p → (q → p)`. Na przykład, jeżeli (`p`) pada
-- deszcz, to jeżeli (`q`) świeci Słońce, to (`p`) pada deszcz. W tym przykładzie może nam
-- przeszkadzać jego *bezsensowność*. Nie wiem, jak Ty, ale ja mógłbym bez zastrzeżeń
-- scharakteryzować taką wypowiedź, gdyby się pojawiła w *potocznej* rozmowie, jako dosyć
-- bezsensowną. No ale w logice używamy odpowiedników słów takich jak "jeżeli", rozumiejąc te słowa
-- technicznie, czyli zgodnie z jednoznacznymi i sztywnymi regułami, a mowa potoczna to takie żywe i
-- barwne i zawsze trochę dzikie "stworzenie".

-- W Leanie, podobnie jak w życiu, funkcje mogą zwracać funkcje:

def dodaje (n : Nat) :=
  (fun (m : Nat) => n + m)

-- Jaki jest typ wyjścia tej funkcji? Jest nim typ funkcyjny, a więc strzałkowy, bo ta funkcja
-- zwraca funkcję, a więc typ funkcji `dodaje` musi mieć postać `Nat → (Nat → Nat)`.

#check @dodaje

-- Lean mówi, że `dodaje : Nat → Nat → Nat`, co znaczy to samo, co `dodaje : Nat → (Nat → Nat)`,
-- ponieważ - jak to się mówi - w Leanie *strzałka wiąże z prawej*.

-- Widzisz już związek z implikacją `p → (q → p)`, o której pisałem na początku?

-- Funkcję `dodaje` możemy zastosować do *jednego* argumentu:

#check dodaje 1 -- Lean tu nie narzeka, a więc to term typu `Nat → Nat`

-- No ale skoro `dodaje 1` ma typ `Nat → Nat`, to znaczy, że cały ten term złożony jest pewną
-- funkcją, którą można zastosować do dowolnej liczby naturalnej:

#check (dodaje 1) 2 -- ten term ma typ `Nat`

-- A ponieważ aplikacja funkcji do argumentu wiąże z lewej, to nawiasy powyżej są zbędne, a więc
-- możemy napisać równoważnie:

#check dodaje 1 2

-- Ten term ma typ `Nat`, bo *jest* (wyrażeniem oznaczającym) pewną liczbą(ę) naturalną.

-- W ten sposób w teorii typów *wszystkie* funkcje mogą być (i są) w istocie *jednoargumentowe*, ale
-- niektórych z nich można używać, *jakby były* wieloargumentowe. A ponieważ w matematyce
-- "używalność jako coś" jest "byciem tym czymś", to te funkcje *są zarazem* jedno i
-- wieloargumentowe. Nazywamy ten sposób curryingiem albo rozwijaniem funkcji.

-- Przy okazji może dodam, że nie możemy ewaluować aplikacji `dodaje 1`, bo to funkcja, a Lean nie
-- umie bez naszej pomocy wyświetlać funkcji:

#eval dodaje 1 -- błąd, ale tylko dlatego, że Lean nie umie nam *pokazać* rezultatu tej aplikacji

-- Zadanie 1: Korzystając z kodu `dodaje` jako wzorca, zdefiniuj funkcję o nazwie `sklejam`, której
-- jedyny parametr będzie miał typ `String` (czyli typ tekstowy), i która będzie zwracała funkcję
-- anonimową, której jedyny (inaczej nazwany!) parametr będzie miał również typ `String`, i która to
-- funkcja anonimowa będzie stosowała znaną Leanowi funkcję `String.append` do obydwu parametrów.

#eval String.append "a" "b" -- Funkcja `String.append` zastosowana do tych argumentów zwraca "ab"

-- Wreszcie sprawdź typ aplikacji `sklejam`, na przykład do argumentów (i zarazem termów) `"co "` i
-- `"nie co"`, i "oblicz" wynik tej aplikacji.

-- Zadanie 2: Traktując `p` i `q` jakby były w zasadzie takimi samymi typami, jak `Nat` czy
-- `String`, i korzystając z kodu funkcji `dodaje` lub `sklejam` jako wzorca, zastąp słowo `sorry`
-- kodem takiej funkcji, żeby całe wyrażenie miało typ `p → (q → p)`, czyli `p → q → p` (no bo
-- strzałka w Leanie wiąże z prawej). Czyli udowodnij to twierdzenie. Nie przejmuj się tym, że
-- parametr funkcji wewnętrznej będzie podświetlony na szaro, bo to tylko *ostrzeżenie*, za pomocą
-- którego Lean nie *wskazuje błędu*, tylko *wyraża troskę* (to ostrzeżenie mówi o niewykorzystanym
-- parametrze).

#check (fun (hp : p) => sorry)

----------------------------------------------------------------------------------------------------
-- KONIUNKCJA JAKO (PEWNEGO RODZAJU) PARA UPORZĄDKOWANA

-- Symbol koniunkcji `∧` uzyskasz pisząc `\and`. Jak już wiesz, jeżeli `p` i `q` to jakieś zdania,
-- to `p ∧ q` czytamy jako `p` i `q`.

-- W logice konstruktywnej `p ∧ q` jest prawdziwe wtedy i tylko wtedy, gdy ma dowód, co ma miejsce
-- wtedy i tylko wtedy, kiedy *oba* zdania mają dowody. Wobec tego jedynym sposobem udowodnienia
-- koniunkcji jest dostarczenie takiej (uporządkowanej) *pary* dowodów.

-- Tą relację *dowiedlności* możemy wyrazić w postaci *implikacji* `p → (q → (p ∧ q))`, którą możemy
-- odczytać jako: jeżeli mam dowód zdania `p`, to jeżeli mam dowód zdania `q`, to mogę uzyskać dowód
-- zdania `p ∧ q`.

-- Czy widzisz, że skoro *jedynym* sposobem udowodnienia koniunkcji jest dostarczenie pary dowodów
-- jej członów, to ostatnia implikacja wyraża wprost coś elementarnego albo fundamentalnego na temat
-- koniunkcji? W szczególności, ta implikacja wyraża (częściowo) bliski związek między *koniunkcją*
-- i *curryingiem*.

-- Lean ma wbudowaną funkcję `And.intro`, która pobiera dwa (jawne) argumenty będące dowodami
-- (jakichkolwiek) dwóch zdań i zwraca dowód koniunkcji tych zdań.

-- Zadanie 3: Opierając się na poprzednich przykładach jako wzorcach i traktując zdania (a więc
-- również `p ∧ q`) jakby to były całkiem zwyczajne typy, udowodnij twierdzenie `p → (q → (p ∧ q))`,
-- korzystając w kodzie funkcji wewnętrznej z `And.intro`.

-- Ponieważ w logice konstruktywnej dowodem koniunkcji jest *uporządkowana para* dowodów jej
-- członów, to dowodzenie zdań zawierających koniunkcje wymaga operowania takimi parami. A
-- uporządkowana para to *cokolwiek*, czego *struktura* albo *funkcjonalność* sprowadza się
-- *całkowicie* do tego, że ma pierwszy i drugi element (każdy określonego typu). Na tym i tylko na
-- tym polega bycie parą uporządkowaną.

-- Zadanie 4: Korzystając z kodu poniżej jako wzorca, udowodnij twierdzenie `(p ∧ q) → q`:

#check (fun (piq : p ∧ q) => piq.left)

-- Ten term ma typ `p ∧ q → p`, czyli `(p ∧ q) → p`, bo koniunkcja wiąże w Leanie mocniej niż
-- implikacja.

-- Nie wiem, czy to widać, więc na wszelki wypadek to podkreślę: uczymy się równolegle pojęć, które
-- mają fundamentalne znaczenie w programowaniu (np. parametr, funkcja-jako-procedura, typy danych,
-- currying), logice (np. spójniki, reguły wnioskowania) i matematyce (np. funkcja, para
-- uporządkowana <i jej związek z curryingiem>).

-- Teraz wiesz w zasadzie wszystko o koniunkcji, bo wiesz, w jaki (jedyny możliwy) sposób ją uzyskać
-- w dowodach i wiesz, jak (na dokładnie dwa sposoby) można jej w dowodach użyć.

-- Wiesz też, w jaki sposób można udowodnić implikację (tworząc funkcję o odpowiadającym jej typie),
-- i wiesz już też w zasadzie, jak jej można użyć, bo użycie w dowodzie implikacji to *nic innego*,
-- jak aplikacja funkcji!:

-- Jeżeli `imp : p → q`, to `imp` jest jednocześnie dowodem implikacji `p → q` i (jakąś) funkcją o
-- typie `p → q`. A zastosowanie tej funkcji do (dowolnego) termu typu `p` ma oczywiście typ `q`. I
-- to się nazywa między innymi "modus ponens", albo (pedantyczniej) "modus ponendo ponens".

-- Tą ostatnią regułę wnioskowania możemy również wyrazić w postaci implikacji - `((p → q) ∧ p) → q`
-- - która może być w tym kontekście nieco dezorientująca, bo zdaje się sugerować związek między
-- *koniunkcją zdań* i *aplikacją funkcji* (do odpowiadającego typowi jej wejścia argumentu). I
-- właściwie taki związek istnieje, bo przecież każda aplikacja to *samo zestawienie*, w
-- *odpowiedniej kolejności*, pewnej funkcji i pewnego argumentu, a to jest *dokładnie* pewnego
-- rodzaju para uporządkowana.

-- Zadanie 5: Spróbujesz udowodnić implikację `((p → q) ∧ p) → q`?

#check (fun (h : (p → q) ∧ p) => sorry)

-- Podpowiem, że w ciele tej funkcji musisz ostatecznie w jakiś sposób uzyskać term typu `q`, a żeby
-- go uzyskać, musisz zastosować funkcję/dowód `p → q` do argumentu będącego dowodem/termem typu
-- `p`, a żeby z kolei uzyskać te dwa termy musisz wydobyć raz pierwszy (albo lewy) a raz drugi
-- (albo prawy) element pary uporządkowanej/dowodu koniunkcji `(p → q) ∧ p`.

----------------------------------------------------------------------------------------------------
-- PRAWDA (JAKO BYCIE?)

#check True -- True : Prop

-- `True` to znane Leanowi szczególne *zdanie atomowe*. Widzimy, że to zdanie, bo term `True` jest
-- typu `Prop`. I to jest zdanie atomowe, bo nie ma żadnej struktury logicznej, nie jest przecież
-- ani koniunkcją zdań, ani implikacją, ani negacją zdania, ani alternatywą, to zdanie ma tylko
-- *nazwę*. I ma też coś jeszcze, co nie ma charakteru zdaniowego.

-- Szczególny charakter zdania `True` polega na tym, że to zdanie jest *aksjomatycznie*, czyli ma
-- nocy *arbitralnego wyboru*, prawdziwe. A skoro prawdziwe znaczy dla nas tyle, co ma dowód, to
-- musi (aksjomatycznie) istnieć dowód tego zdania. W Leanie ten dowód nazywa się `True.intro`. I to
-- w zasadzie wszystko, co można powiedzieć o tym typie (i tym zdaniu).

-- Można więc chyba (również) powiedzieć, że w ten sposób wyrażamy formalnie ideę, że *istotą prawdy jest
-- istnienie*; sum, ergo sum, ἐγώ εἰμι, i tak dalej ;-)

#check True.intro -- True.intro : True

-- Zadanie 6: Udowodnij zdanie `p → True`.

-- Czy widzisz, że zdanie `True` wynika (pusto, "czysto formalnie" albo wręcz "niematerialnie") z
-- każdego zdania?
