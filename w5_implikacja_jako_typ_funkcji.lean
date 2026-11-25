-- Tak w Leanie piszemy komentarze. Komentarze są przez Leana ignorowane.

-- Najpierw objaśnię sedno sprawy w maksymalnym (i dla początkujących niezbyt zrozumiałym) skrócie:

-- Zdefiniowana w Leanie funkcja `Nat.succ` zwraca następną liczbę naturalną, na przykład:
#eval Nat.succ 1 -- `2`

-- To *definicja* (`def ... := ...`) stałej o nazwie `ss` jako funkcji, która pobiera argumenty typu
-- `Nat` (`(n : Nat)`) i zwraca rezultat typu `Nat` (`: Nat`). Ta funkcja (w swoim *ciele*)
-- dwukrotnie stosuje funkcję `Nat.succ`:
def ss (n : Nat) : Nat := Nat.succ (Nat.succ n)

#eval ss 1 -- `3`

-- Gdy *zestawiamy* ze sobą funkcję `ss` i jakiś akceptowalny przez nią *argument*, uzyskujemy w ten
-- sposób *od razu, jeszcze przed obliczeniem wyniku*, term typu `Nat`, bo samo takie zestawienie
-- (nazywane *aplikacją*) jest już opisem pewnej liczby naturalnej:
#check ss 1 -- `ss 1 : Nat`

-- Gdy kursor znajduje się na linii `#eval ...` powyżej, Lean *rozpakowuje definicję* stałej `ss`.
-- Treścią tej definicji jest funkcja *anonimowa*, ...
#check (fun (n : Nat) => Nat.succ (Nat.succ n)) -- `... : Nat → Nat`

-- ... a ponieważ pojawia się tam argument `1`, to uzyskujemy (po rozpakowaniu definicji `ss`) taką
-- oto aplikację o typie `Nat`:
#check (fun (n : Nat) => Nat.succ (Nat.succ n)) 1 -- `... : Nat`

-- Ewaluacja (która w a tym wypadku jest nazywana też *redukcją*) tej aplikacji polega na tym, że
-- Lean *odrywa ciało funkcji*, czyli część definicji funkcji występującą po symbolu `=>`, ...

-- `Nat.succ (Nat.succ n)`

-- ... i *podstawia argument we wszystkie miejsca wystąpienia parametru*:
#check Nat.succ (Nat.succ 1) -- `... : Nat`

-- Lean w ten sam sposób ewaluuje (redukując przez podstawianie i odrzucanie części `fun ... =>`)
-- aplikację `Nat.succ 1`, a gdy już obliczy rezultat (`2`), tak samo ewaluuje `Nat.succ 2`.
-- Ponieważ rezultat tej ostatniej aplikacji (`3`) *nie* jest już aplikacją, ewaluacja się na tym
-- kończy.

-- Dlatego każdą definicję funkcji można rozumieć jak pudełko, które ma jedno lub więcej wejść
-- określonego typu (tutaj `(n : Nat)`), jedno wyjście określonego typu (tutaj `Nat`), a w środku
-- którego to pudełka są "przewody" od wejść do jakiś wewnętrznych pudełek (czyli innych funkcji
-- aplikowanych do parametrów w ciele tej funkcji, tutaj `Nat.succ`), których wyjścia, być może
-- przechodząc przez jakieś wewnętrzne pudełka (tutaj wyjście "pierwszego" pudełka `Nat.succ` jest
-- podłączone do jeszcze jednego pudełka `Nat.succ`), ostatecznie zmierzają do wyjścia definiowanej
-- funkcji.

-- Na przykład, definicję `ss` można by (w wymyślonej przeze mnie notacji) "zobrazować" tak,
-- interpretując `:` jako zewnętrzny "interfejs" a `-->` jako "przewody kierunkowe":

-- `Nat : --> Nat.succ --> Nat.succ --> : Nat`

-- Czytamy to: Pobieram `Nat-y`, które przepuszczam przez maszynkę `Nat.succ`, a wynik przepuszczam
-- jeszcze raz przez `Nat.succ`, i zwracam rezultat (typu `Nat`). Zastosowana tu "graficzna" notacja
-- "przewodowa" sprawia, że *nazwy parametrów stają się całkowicie zbędne*, ponieważ de facto *są*
-- zbędne:

-- *Parametry to oznaczenia połączeń między funkcjami, z aplikacji których składa się dana funkcja*.

-- Gdyby w Leanie można było robić tylko takie rzeczy, byłby to język programowania funkcyjnego jak
-- każdy inny. Ale można robić w nim również takie rzeczy (i w zasadzie właśnie to sprawia, że w
-- Leanie można sformalizować praktycznie całą matematykę):

def uogólniona_identyczność (typ : Type) (parametr : typ) : typ := parametr

-- Tą funkcję można stosować do argumentów różnego typu, trzeba jej tylko powiedzieć, jakiego:
#eval uogólniona_identyczność Nat 1 -- 1
#eval uogólniona_identyczność String "2" -- "2"

-- Typ funkcji `uogólniona_identyczność` to przykład *typu zależnego* (przez co ta funkcja jest
-- *polimorficzna*), bo to, *jakiego typu jest ta funkcja, zależy od argumentu*, który podamy jej na
-- wejściu. Konkretnie, *typ* drugiego parametru jest tu *wartością* pierwszego parametru:

-- `uogólniona_identyczność Nat 1` --> (rozpakowanie definicji)
-- `(fun (typ : Type) => (fun (parametr : typ) => parametr)) Nat 1` --> (oderwanie ciała i podstawianie)
-- `(fun (parametr : Nat) => parametr) 1` --> (oderwanie ciała i podstawianie)
-- `1`

-- A teraz bardziej rozwlekle i trochę inaczej.

----------------------------------------------------------------------------------------------------
-- TERMY, TYPY, FUNKCJE, SPRAWDZANIE TYPU I EWALUACJA

-- Gdy kursor znajduje się na linii jakiegoś kodu, a Lean został poprawnie zainstalowany i
-- zintegrowany z edytorem Visual Studio Code, w panelu po prawej będą się pojawiać różne
-- komunikaty. Na przykład, gdy umieścisz kursor na linii poniżej, ...

#eval 665 + 2

-- ... zobaczysz po prawej liczbę `667`. Komenda `#eval` mówi Leanowi, żeby coś "poddał ewaluacji",
-- co akurat tutaj polega na obliczeniu wyniku dodawania.

-- Będziemy pisać tak zwane *termy* w języku *teorii typów* (zależnych). Każdy term ma unikalny
-- *typ*. Unikalny znaczy w matematyce *dokładnie jeden* (danego rodzaju). Możemy zapytać Leana,
-- jaki typ ma term `2`, posługując się komendą `#check`:

#check 2

-- Gdy kursor znajduje się na linii powyżej, Lean mówi nam (po prawej), że `2` ma typ `Nat`, czyli,
-- że jest liczbą naturalną i to jest *jedyny* typ, który ten term ma. Ogólnie, `X : Y`, gdzie `X` i
-- `Y` to jakieś (być może złożone) termy, czytamy w Leanie: term `X` ma (tylko) typ `Y`, albo
-- krócej, `X` ma typ `Y`, a czasem nawet `X` jest `Y`.

-- Każdy typ jest również termem! Ale nie każdy term jest typem! Na przykład, `Nat` to jednocześnie
-- term i pewien typ, ale `2` to nie jest żaden typ, bo to jest *tylko* term. Podobnie w życiu,
-- konkretna bułka (albo, jak mówią filozofowie, jej "token") jest obiektem typu bułka, ale raczej
-- nie jest żadnym typem. Natomiast typ bułka, to jest bółkę w ogólności, również można, jeśli się
-- chce, traktować jako pewnego rodzaju obiekt, tyle, że abstrakcyjny.

-- Tak przy okazji, term `Nat` jest typu `Type`, bo jest takim dosyć zwyczajnym typem, ...

#check Nat -- Nat : Type

-- ... term `Type` to tak naprawdę term `Type 0`, który z kolei jest typu `Type 1`, ...

#check Type -- Type : Type 1

-- ... i tak dalej. Mamy tu więc nieskończoną hierarchię typów, ale mało co jest w tej hierarchii
-- ciekawe i nie jest to wcale niezbędny element języka teorii typów.

-- Typy są trochę jak zbiory i trochę jak pojęcia albo kategorie albo rodzaje, ale nie całkiem, bo
-- relacja bycia typem *nie* jest w Leanie przechodnia. Na przykład, `Nat` *nie* ma typu `Type 1`.
-- Bo typ każdego termu, jak już wspominałem, jest unikalny.

-- Jeżeli chcesz, możesz myśleć o tym jako o czymś w rodzaju "etykietowania". Każdy produkt w
-- sklepie (term) ma unikalną etykietę (typ), ale poza tym ta analogia też się sypie, bo etykiety
-- raczej nie mają swoich etykiet. Ale jeśli chcesz tak czasem myśleć, to śmiało.

-- Będziemy się uczyć logiki zdań i logiki predykatów korzystając z *odpowiedniości
-- Curry'ego-Howarda*. Pozwoli nam ona uczyć się *jednocześnie* logik (liczba mnoga), programowania,
-- i podstaw formalnych (całej!) matematyki. Ceną, jaką musimy za to zapłacić, jest konieczność
-- przyzwyczajenia się do tego, że pewne rzeczy będziemy postrzegali (niemal) jednocześnie z więcej
-- niż jednej perspektywy. To znaczy, będziemy rozmaite struktury i procesy (niemal) równocześnie
-- interpretować na więcej niż jeden sposób. Początkowo będzie przez to trudniej, ale później
-- powinno się dzięki temu zrobić (znacznie) łatwiej, niż gdybyśmy do tego podeszli w bardziej
-- tradycyjny sposób.

-- Nawiasem mówiąc, od pewnego momentu będziemy się zastanawiać nad kwestiami istnienia, statusu i
-- charakteru rozmaitych *perspektyw*, *interpretacji*, czy *punktów widzenia*, między innymi
-- dlatego, że ważnych i niewykluczających się punktów widzenia czy perspektyw jest w psychologii
-- trochę. Szczególnie zaś będzie nas interesowało to, kiedy i w jakim sensie tego rodzaju "rzeczy"
-- możemy *poprawnie* czy może raczej *zasadnie wybierać*.

-- Dlaczego mielibyśmy się uczyć logik, programowania i podstaw matematyki na kursie dotyczącym
-- metod teoretycznych w psychologii?
--
-- Logik, ponieważ, o czym zdążyliśmy się już przekonać, to będą nasze formalne narzędzia służące do
-- formalizacji rozumowań, co jest niewątpliwie jednym ze sposobów uprawiania analizy
-- (meta)teoretycznej. Jakieś rodzaje logik odgrywają również ważną rolę na przykład w procesie
-- terapii, bo przecież terapeci często próbują ułatwić swom pacjentom odkrywanie *niespójności* w
-- ich zachowaniach i przekonaniach, a w logikach poprawność formalna to właśnie między innymi (w
-- taki albo inny sposób rozumiana) spójność.
--
-- Programowania będziemy się uczyć między innymi dlatego, że teorie psychologiczne bywają wyrażone
-- w postaci procedur symulacji, czyli w (wykonywalnym) kodzie, a zatem, żeby je dobrze zrozumieć,
-- trzeba mieć jakieś pojęcie o programowaniu. A poza tym na przykład terapia to przecież pomoc w
-- przeprogramowywaniu się. No i prawie każde badanie psychologiczne polega na (konsensualnym)
-- programowaniu osób badanych za pomocą instrukcji.

-- A podstaw matematyki będziemy się uczyć dlatego, że niektóre z bardziej dopracowanych teorii
-- psychologicznych mają postać przynajmniej częściowo formalną. Byłoby też wspaniale, gdybyśmy
-- nabrali pewnej orientacji w tym, na czym może polegać *matematyzacja teorii* (to wcale nie musi
-- być i zwykle nie jest formalizacja rozumowań). Niestety, trudno (mi w tej chwili) powiedzieć,
-- jaki to ma związek na przykład z terapią.

-- Term to wyrażenie poprawne w języku teorii typów. Poprawność wyrażenia, czyli jego "termowość",
-- poznajemy w Leanie po tym, że to wyrażenie ma jakiś typ, czyli, że jest *typowalne*. Wszystko, co
-- będzie dla nas robił Lean, będzie polegało albo na ewaluacji (zastosowania jakiś funkcji do jakiś
-- argumentów), albo na typowaniu, czyli na ustalaniu typów wyrażeń typowalnych lub ustalaniu faktu,
-- że jakieś wyrażenia nie są typowalne, czyli są błędne, czyli nie są termami. Na przykład, to
-- wyrażenie jest błędne, a wobec tego nie jest termem, bo nie ma typu, ponieważ Lean nie wie, jak
-- ma zastosować dodawanie do liczby i *fragmentu tekstu* (którym jest term `"2"`):

#check 2 + "2" -- Lean sygnalizuje błędy w kodzie za pomocą podkreślenia falistą czerwoną linią.

-- Poza typowalnością, naszym najważniejszym pojęciem będzie pojęcie *funkcji*. To jest w ogóle dość
-- ważne pojęcie. Niektórzy nawet twierdzą, że to jest najważniejsze pojęcie w całej matematyce.
-- Zresztą w psychologii też interesują nas przede wszystkim pewne (dosyć szczególne) funkcje, to
-- jest takie, które (w sposób nie całkiem przewidywalny <i to jest ta ich szczególność>)
-- przekształcają bodźce w reakcje.

-- Przez pewien czas będziemy rozumieli funkcje jako *wykonywalne procedury komputerowe*, albo
-- "formalne mechanizmy", albo po prostu *przepisy* (jak coś z czegoś zrobić). Najprostszą funkcją,
-- która coś robi z termami typu `Nat` (mówimy też, że ta funkcja jest określona na typie `Nat`),
-- jest funkcja identycznościowa, która akurat nic nie robi. Możemy ją zdefiniować w Leanie na
-- przykład tak:

def idnat (n : Nat) := n

-- Czytamy to: Definiuję (`def`) stałą o nazwie `idnat` jako funkcję, która, gdy podamy jej na jej
-- (jedynym) wejściu term o typie `Nat` (`(n : Nat)`), który akurat dla tej funkcji (albo z jej
-- perspektywy) ma nazwę `n`, to zwraca ten term. Nic innego z nim nie robi, tylko go zwraca, co
-- właśnie czyni ją funkcją identycznościową (inaczej identycznością). Wbrew pozorom to bardzo ważny
-- rodzaj funkcji.

#eval idnat 7 -- Lean twierdzi, że `7`

-- Nazwy parametrów funkcji są widoczne jako takie tylko wewnątrz ciała funkcji. Ciało funkcji to ta
-- część definicji funkcji, która pojawia się po symbolu definiowania `:=`. W szczególności, `n` nie
-- jest tu termem, tylko w pewien sposób oznaczonym *wejściem*; tylko ciał(k)o funkcji `idnat`, gdy
-- na skutek ewaluacji przetwarza jakiś podany na wejściu term, "widzi" to `n` jako term typu `Nat`:

#check n

-- Lean sygnalizuje tutaj błąd, bo jak dotąd symbol `n` ma określony typ tylko w ciele funkcji
-- `idnat`.

-- Może użyteczna metafora: Funkcja-jako-program jest jak pudełko, które ma zawsze dokładnie jeden
-- "otwór wyjściowy" i co najmniej jeden "otwór wejściowy" (a tak naprawdę zawsze dokładnie jeden, o
-- czym kiedy indziej). Każdy z tych otworów ma określony "kształt" (czyli typ), co sprawia, że nie
-- można podawać funkcjom na wejściach czegokolwiek. Na przykład, nie wsadzimy, nie uszadzając jej
-- przy tym, (standardowej dorosłej) kury do otworu wejściowego w kształcie (standardowego
-- dorosłego) chomika. *Od środka* te otwory są oznaczone nazwami, które mogą też występować w
-- "przepisie" (czyli ciele definicji funkcji). Ten przepis czyta taki niewysoki wąsaty i szczupły
-- facecik (czyli Lean <ten sam w każdej funkcji!>), który go (to znaczy ten przepis) stosuje, gdy
-- go (to znaczy Leana) o to ładnie poprosimy.

-- Wybrałem arbitralną nazwę `idnat`, bo tak, i ta nazwa ma odtąd status zdefiniowanej *stałej*.

-- Lean domyśla się, że w tej definicji chodzi nam o funkcję, ponieważ zaraz po nazwie stałej
-- pojawia się wyrażenie `(n : Nat)`, określające parametr. Dla porównania, to jest definicja stałej
-- o typie `Nat`, w której nie ma specyfikacji parametru:

def dwa : Nat := 3

-- Stała `dwa` oznacza odtąd liczbę `3`. I to oczywiście nie jest funkcja, bo nie ma żadnego wejścia
-- (chociaż można tą stałą tak konsekwentnie interpretować! ale o tym może nawet nigdy).

-- A to jest funkcja dodająca do dowolnej liczby naturalnej liczbę `1` (tym razem inaczej nazwałem
-- parametr, żeby zilustrować w ten sposób fakt, że parametry możemy nazywać niemal całkiem
-- dowolnie):

def nast (liczba : Nat) := liczba + 1

-- A to jest wynik zastosowania tej ostatniej funkcji do liczy `4`:

#eval nast 4 -- Lean twierdzi, że `5`

-- Obie powyższe funkcje mają ten sam typ (pomijając nazwy parametrów, które nie decydują o
-- tożsamości funkcji):

#check idnat -- idnat (n : Nat) : Nat
#check nast -- nast (liczba : Nat) : Nat

-- Lean może pokazać te typy w inny sposób, to jest w pewnym sensie bardziej wprost, gdy użyjemy
-- takiej oto składni (dopisujemy z przodu `@`) i wtedy od razu widać, że obie funkcje mają ten sam
-- typ:

#check @idnat -- idnat : Nat → Nat
#check @nast  --  nast : Nat → Nat

-- To będzie dla nas niebawem ważne: Przypominam, że `X : Y` czytamy jako term `X` jest typu `Y`. A
-- więc `idnat : Nat → Nat` czytamy jako: term `idnat` ma typ `Nat → Nat`. To przykład *typu
-- strzałkowego*, inaczej *typu funkcji*. Przed strzałką mamy typ argumentu, który może przyjąć i
-- przetworzyć dana funkcja, a po strzałce mamy typ rezultatu jej zastosowania. Mówiąc jeszcze
-- inaczej, `idnat` jest funkcją z `Nat`-ów do `Nat`-ów, albo posyłającą `Nat`-y w `Nat`-y, albo
-- jest endofunkcją na typie `Nat`, albo jest mapowaniem `Nat`-ów w `Nat`-y, jak również jest "na",
-- ale tymi wszystkimi alternatywnymi sposobami mówienia się w ogóle nie przejmuj.

-- Jeżeli teraz *poddamy ewaluacji zastosowanie* (samo *zestawienie termów* `idnat 2`, jeszcze
-- *przed* obliczeniem wyniku, jest w naszej terminologii już zastosowaniem, inaczej *aplikacją*
-- funkcji) tej funkcji do termu `2`, to zobaczymy jako wynik `2`:

#eval idnat 2

-- A to przykład tej samej aplikacji (tej samej funkcji do tego samego argumentu), którego nie
-- poddajemy (w tym miejscu) ewaluacji, bo tylko sprawdzamy typ:

#check idnat 2 -- idnat 2 : Nat

-- Jak widać, czasami warto odróżnić tak rozumianą *aplikację funkcji do argumentu* od *ewaluacji
-- takiej aplikacji*. Bo czasem, zwłaszcza zaś - jak zobaczymy - w logice, obchodzi nas *tylko*
-- poprawność lub typ tego rodzaju aplikacji, a *nie* jej wynik.

-- Zadanie 1: Zdefiniuj (bez użycia AI!) funkcję `plus2`, która będzie dodawała do dowolnej liczby
-- naturalnej liczbę `2`, przeczytaj tą definicję zgodnie z podaną wcześniej konwencją, a na koniec
-- sprawdź typ i oblicz wynik zastosowania tej funkcji do liczby `6`, używając komend `#check` i
-- `#eval`.

-- Tak możemy zdefiniować funkcję *dwuargumentową*, która dodaje liczby naturalne:

def suma (m : Nat) (n : Nat) := m + n

-- Tak naprawdę to funkcja jednoargumentowa, która pobiera jedną liczbę naturalną i *zwraca funkcję
-- jednoargumentową*, która z kolei przekształca jedną liczbę naturalną w liczbę naturalną. Ale o
-- tym kiedy indziej. Tylko to teraz sygnalizuję; o tym też możesz na razie spokojnie zapomnieć.

#eval suma 1 2 -- Lean twierdzi, że `3`

-- Dobrze, ale co to wszystko ma wspólnego z logiką? No więc okazuje się, że takie programowanie i
-- logika to (prawie) to samo, a mówiąc dokładniej, programowanie i matematyka to to samo, tylko
-- inaczej rozumiane (i często też inaczej używane).

----------------------------------------------------------------------------------------------------
-- TYP Prop, ZDANIA JAKO TYPY, DOWODY ZDAŃ JAKO TERMY TYPÓW ZDANIOWYCH, IMPLIKACJA JAKO TYP FUNKCJI

-- W ten sposób mówimy Leanowi, że chcemy się przekonać, co można w tym języku powiedzieć poprawnie
-- na temat jakiś *bliżej nieokreślonych* termów `p`, `q` i `r` typu `Prop`. `Prop` to specjalny
-- typ, który można czytać jako "Zdanie" (`Prop` to skrót od angielskiego "Proposition"). A więc
-- mówimy w ten sposób, że mamy ochotę coś zrobić z trzema bliżej nieokreślonymi zdaniami.

variable (p q r : Prop)

#check p -- `p : Prop`

-- Tak oto, mocą naszej decyzji, `p : Prop`, czyli `p` ma typ `Prop`, czyli `p` jest *jakimś*
-- zdaniem. No a logika dotyczy (między innymi) zdań, co nie?

-- Symbol strzałki `→` uzyskasz pisząc `\to`.

#check p → p -- `p → p : Prop`

-- Skoro `p` to zdanie, a `→` ze zdania do zdania oznacza implikację, to `p → p` jest również
-- zdaniem, które można odczytać jako "Jeżeli `p`, to `p`". Nawiasem mówiąc, można powiedzieć, że
-- implikacja to najważniejszy spójnik w logice. Ale z drugiej strony właściwie wszystko *można*
-- powiedzieć (chociaż nie wszystko zawsze wypada, należy, lub warto).

-- To teraz uważaj: W teorii typów jest *jednocześnie* prawdą, że `p → p` to typ funkcji!

-- Ale może po kolei: W logice konstruktywnej, inaczej intuicjonistycznej, której się teraz uczymy,
-- zdanie prawdziwe znaczy dokładnie to samo, co zdanie mające dowód. W logice *klasycznej* ta
-- interpretacja jest zbyt mocna, bo logika klasyczna zakłada "luźniejsze" pojęcie prawdy. Wszystko,
-- co można udowodnić w logice konstruktywnej, można też udowodnić w logice klasycznej, ale nie
-- odwrotnie, bo w logice klasycznej obowiązuje dodatkowo *zasada wyłączonego środka*, ...

-- *Dla każdego zdania `z`, `z` lub nie `z`*.

-- ... równoważna *zasadzie podwójnej negacji*, ...

-- *Dla każdego zdania `z`, jeżeli nieprawda, że nieprawda, że `z`, to `z`*.

-- ... która *nie* obowiązuje (uniwersalnie) w logice konstruktywnej, ponieważ nie każde
-- matematyczne zdanie prawdziwe da się w matematyce udowodnić. Ale o tym może kiedy indziej.

-- To teraz znowu uważaj: Termy typu `Prop` są w naszej teorii typami! A więc nie tylko `Prop` to
-- term oznaczający typ (tutaj akurat typ zdań), ale również termy typu `Prop` to typy. W
-- szególności, `p`, `q` i `r` to zdania i jednocześnie typy (bo każde zdanie w teorii typów jest
-- typem). A co jest termem typu zdaniowego `p`? Jest nim każdy *dowód* `p`. To nie musi mieć w tej
-- chwili dla Ciebie żadnego sensu, ale to jest coś, co trzeba chwilowo *zaakceptować jako
-- konwencję* (albo interpretację, albo perspektywę, albo punkt widzenia). Po prostu tak się tylko
-- umawiamy, żeby zobaczyć, co z tego wyniknie.

-- Wobec tego w teorii typów jest *jednocześnie* prawdą, że:
--
-- `p → p` to typ funkcyjny, czyli typ funkcji, które w jakiś sposób przekształcają termy typu `p` w
-- termy typu `p`.
--
-- `p → p` to typ funkcyjny, czyli typ funkcji, które w jakiś sposób przekształcają dowody zdania
-- `p` w dowody zdania `p`.
--
-- `p → p` to typ zdaniowy, którego termy są dowodami zdania `p → p`.
--
-- `p → p` to implikacja, która oznacza, że ze zdania `p` wynika zdanie `p`.
--
-- Jeżeli w jakikolwiek sposób uda nam się skonstruować term typu `p → p`, czyli tak działającą
-- funkcję, to udowodnimy (konstruktywnie) zdanie `p → p`.

-- Możemy to zrobić na wiele sposobów, ale zaczniemy od takiego, który pozwoli nam wyraźnie zobaczyć
-- tą wspaniałą "wieloznaczność". Żeby to zrobić, musimy wprowadzić pojęcie *funkcji anonimowej*,
-- czyli funkcji, która nie ma nazwy, czyli takiej, która nie jest "treścią" żadnej stałej.

#check (fun (n : Nat) => n + 1) -- `fun (n : Nat) => n + 1 : Nat → Nat`

-- Lean nam mówi, że `(fun (n : Nat) => n + 1)` to funkcja przekształcająca `Nat`-y w `Nat`-y, co
-- znaczy, że to jest term o typie `Nat → Nat`. Zwracam uwagę, że przed ciałem w taki sposób
-- zapisanej funkcji piszemy `=>`, a nie `:=`, bo tu nie chodzi o *definiowanie* `fun (n : Nat)`,
-- tylko o *określenie sposobu działania na parametrach*.

-- Funkcje anonimowe możemy stosować tak, jak każde inne:

#check (fun (n : Nat) => n + 1) 2

-- Ten term (złożony) ma typ `Nat`, bo samo zastosowanie tej funkcji do liczby naturalnej *jest* już
-- liczbą naturalną, tak jak zastosowanie funkcji kwadratowej do liczby rzeczywistej, jeszcze przed
-- obliczeniem wyniku, takie jak 2², *jest* już - w pewien sposób zapisaną - liczbą rzeczywistą.

#eval (fun (n : Nat) => n + 1) 2 -- Lean twierdzi, że `3`

-- Pytanie, czy zdanie `p → p` jest twierdzeniem logiki, możemy teraz rozumieć jako pytanie, czy
-- istnieje term typu `p → p`, czyli, czy istnieje (jakakolwiek) funkcja z typu `p` do typu `p`.
-- Żeby *skonstruować* taką *funkcję*, nie musimy dysponować żadnym konkretnym termem typu `p`,
-- czyli dowodem zdania `p`. Podobnie, żeby skonstruować funkcję z `Nat` do `Nat`, co nie wymagało
-- jeszcze jej stosowania, nie korzystaliśmy z żadnej konkretnej liczby naturalnej.

-- Żeby sprawdzić, czy poszukiwana funkcja "działa", czyli, czy jest faktycznie dowodem zdania `p →
-- p`, musimy więc tylko sprawdzić jej typ. I to będzie Twoje zadanie.

-- Zadanie 2: Zastąp słowo kluczowe `sorry` czymś, co sprawi, że uzyskasz funkcję anonimową będącą
-- termem o typie `p → p`, czyli sprawi, że udowodnisz zdanie `p → p`, tym samym przyznając mu
-- status *twierdzenia*:

#check (fun (jakis_dowod_p : p) => sorry)

-- Gdy umieszczamy słowo kluczowe `sorry` w miejscu, które (być może) uzupełnimy za pomocą
-- odpowiedniego kodu później, Lean nie narzeka, że czegoś brakuje.

-- A teraz popatrzmy raz jeszcze, co się właściwie tutaj, to znaczy w logice konstruktywnej
-- uprawianej za pomocą języka teorii typów (obsługiwanego przez asystenta dowodzenia Lean), dzieje:

-- Umawiamy się, że zdanie prawdziwe = zdanie posiadające (jakiś) dowód.
--
-- Zdania to termy typu `Prop` i jednocześnie typy swoich dowodów. Inaczej mówiąc, każdy term
-- zdania-jako-typu jest dowodem tego zdania. A wszystkie takie termy są (czasami hipotetycznymi!)
-- programami komputerowymi.
--
-- Jeżeli `p : Prop`, to `p → p` to również zdanie i jednocześnie typ funkcji, które przekształcają
-- termy typu `p`, czyli dowody zdania `p`, w termy typu `p`, czyli dowody zdania `p`.
--
-- Każda implikacja jest szczególnym przypadkiem typu funkcyjnego, a każdy dowód implikacji to pewna
-- funkcja.
--
-- Prawdziwość `p → p` to (przypominam, że w logice konstruktywnej) dokładnie to samo, co istnienie
-- dowodu zdania `p → p`, a to jest dokładnie to samo, co istnienie funkcji, która z dowolnego
-- dowodu zdania `p` robi (w jakikolwiek sposób) dowód zdania `p`.
--
-- Jeżeli `p`, to `p`. Mając jakiś dowód `p`, zawsze można zrobić dowód `p`. Czy nie wydaje Ci się
-- teraz oczywiste, że to (prawie) to samo?

-- Jeżeli nie udało Ci się jeszcze zrobić ostatniego zadania, to zastanów się proszę, co takiego
-- musi robić funkcja, która dostaje na wejściu dowody zdania `p`, żeby dała nam na wyjściu dowód
-- zdania `p`? Podpowiem tylko, że bardzo niewiele.
