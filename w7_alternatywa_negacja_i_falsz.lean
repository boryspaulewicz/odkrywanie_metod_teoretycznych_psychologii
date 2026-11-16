----------------------------------------------------------------------------------------------------
-- ALTERNATYWA, NEGACJA I FAŁSZ

variable (p q r : Prop)

-- Implikacja to typ pewnego rodzaju funkcji, to jest takiej, która przekształca dowody jakiegoś
-- zdania w dowody jakiegoś (być może innego) zdania. Skoro to jest typ funkcji, to również jakiegoś
-- *procesu*. Koniunkcja to typ *statycznej* struktury danych, konkretnie typ uporządkowanych par
-- dowodów zdań. Podobnie jak "zwyczajne" funkcje, implikacje coś "robią", i może właśnie (między
-- innymi) dlatego oznaczamy jedne i drugie za pomocą strzałki. Koniunkcja to bardziej takie bycie
-- razem. W naszej logice prawda również nic nie robi, bo tylko jest i nie ma wewnętrznej struktury.
-- Dlatego można właściwie powiedzieć, że prawda jest tutaj byciem lub bytem jako takim.

----------------------------------------------------------------------------------------------------
-- FAŁSZ

-- Istnieje również zdanie ...

#check False -- False : Prop

-- ... które ma tą właściwość, że *nie istnieje dowód tego zdania*. A więc to - raz na zawsze -
-- *tylko* (puste) zdanie, znane też, szczególnie fanom pewnego osobnika, zdaje mi się, szukającego
-- swojego miejsca na ślepo tam, gdzie nic nie ma, jako fake news.

-- Technicznie, ta własność polega na tym, że `False` jest typem, który z definicji, albo
-- aksjomatycznie, nie posiada konstruktora. Termy mające typ implikacji konstruujemy za pomocą
-- słowa kluczowego `fun`, termy mające typ koniunkcji za pomocą `And.intro`, term typu `True` jest
-- tylko jeden i jest nim konstruktor bezargumentowy `True.intro`, a `False` jest tym, czym jest,
-- właśnie dlatego, że ten typ nie ma konstruktora.

-- (Może masz ochotę umieścić kursor nad stałą `False`, występującą po komendzie `#check`, kliknąć
-- prawy klawisz myszy i wybrać opcję "Przejdź do definicji"?)

-- Prawda wynika (pusto, bo w sposób, który nie polega na korzystaniu z dowodu innego niż zawsze
-- dostepny dowód `True`) ze wszystkiego; z `False` wynika wszystko (w dodatku jeszcze bardziej
-- pusto, chociaż *pozornie* niepusto):

example : False → p := fun (hF : False) => hF.elim

-- `hF` to tutaj *parametr* funkcji; żeby funkcja miała *dobrze określony* parametr, *nie* musi
-- istnieć term typu odpowiadającego temu parametrowi. Czytamy to, trochę niezgrabnie:
--
-- Czy na przykład (`example :`) typ `False → p` ma term zapisany po symbolu definiowania?
--
-- W ten sposób sprawdzamy nie tylko typowalność termu, ale również to, czy dany term ma pewien
-- *podany jawnie* typ, tutaj akurat typ `False → p`. Możemy używać tej konwencji we wszelkich
-- dowodach, na przykład (pominąłem tym razem nawiasy wokół specyfikacji parametru, bo tak czasami
-- można):

example : p → p := fun hp : p => hp

-- Skoro Lean nie narzeka, to term `fun hp : p => hp` jest poprawnym dowodem zdania `p → p`.

-- Można to zapisać jeszcze krócej, bo Lean umie tu wywnioskować typ parametru:

example : p → p := fun hp => hp

-- To samo można udowodnić też tak, bo dowód tego twierdzenia to szczególny przypadek funkcji
-- identycznościowej (na dowodach), która (w postaci uogólnionej) nazywa się w Leanie `id`:

example : p → p := id

-- Ale już wróćmy do fałszu. Aksjomatyczną konwencję, że z fałszu wynika wszystko, czyli, że (zawsze
-- tylko hipotetyczny) term typu `False` *mógłby* zostać użyty, żeby udowodnić dowolne zdanie,
-- nazywamy *zasadą eksplozji dedukcyjnej*, a po łacinie ex falso (sequitur) quodlibet. Nie ma w tym
-- chyba nic szczególnie intuicyjnego, może poza tym, że *nie da się wykazać, że nie jest prawdą*,
-- że `False → p`, ponieważ nie da się nigdy wywołać tego typu funkcji i przekonać się w ten sposób,
-- że ta funkcja nie działa, bo żaden term typu `False` nie istnieje i wobec tego nie ma niczego, do
-- czego można by funkcję tego typu aplikować. Tego rodzaju implikacje są zatem zawsze spełnione
-- pusto.

----------------------------------------------------------------------------------------------------
-- NEGACJA

-- Negacja to (nie tylko) w Leanie "tak naprawdę" *implikacja* do zdania/typu `False`. Symbol
-- negacji `¬` uzyskasz pisząc `\neg`.

#check ¬p -- ¬p : Prop

-- Jeśli umieścisz kursor nad termem `¬p`, występującym po komendzie `#check`, to Lean pokaże Ci
-- okno pomocy, w którym wyjaśni, że negacja to właśnie implikacja do fałszu w przebraniu zwięzłej
-- notacji.

-- A skoro z fałszu wynika każde zdanie, negacja zdania to implikacja z tego zdania do fałszu, a
-- implikacja to funkcja, którą można aplikować, uzyskując term typu będącego następnikiem tej
-- implikacji, to nie tylko możemy *aplikować negacje*, ale również ze sprzeczności wynika wszystko.
-- Może nie od razu to widać, ale można to łatwo udowodnić.

-- Zadanie 1: Zastąp `sorry` aplikacją dowodu/funkcji/termu typu zdaniowego `¬p` do dowodu/termu
-- typu zdaniowego `p`. Musisz tylko wydobyć te (hipotetyczne) dowody z (hipotetycznego) dowodu
-- koniunkcji, którym jest `h`, i zapisać je w odpowiedniej kolejności, tak jak to robiliśmy
-- wcześniej, używając (dowodów) koniunkcji w dowodach. Ponieważ (czysto hipotetyczny) rezultat tej
-- aplikacji jest typu `False`, to wywołanie na rzecz (czysto hipotetycznego) termu tego typu tak
-- zwanej składowej `elim` (to właśnie tutaj robimy) pozwala udowodnić każde zdanie.

example : (p ∧ ¬p) → q := (fun h : (p ∧ ¬p) => (sorry).elim)

-- I to jest wszystko, co trzeba wiedzieć o negacji. Może warto tylko dodać, że z tej perspektywy
-- negacja to niemal dosłownie droga doNikąd i zarazem Pusta obietnica.

-- Widzimy więc, choćbyśmy nawet nie chcieli, że - całkiem dosłownie - w każdej negacji kryje się
-- Fałszywość. A także Absolutny Brak, przez co negacja odpowiada temu, co według św. Tomasza z
-- Akwinu jest samą istotą Grzechu.

-- I jak tu nie popaść w (niekoniecznie teistyczny <i czy aby na pewno taki całkiem pop?>)
-- mistycyzm?

-- Że co?!

----------------------------------------------------------------------------------------------------
-- ALTERNATYWA

-- Jeżeli koniunkcja to takie jakby bycie razem, albo współbycie (albo może obcowanie?), to
-- alternatywa to taki jakby *wybór*, albo *możliwość*, a może nawet wręcz najprostsza postać
-- *niepewności*.

-- Symbol alternatywy `∨` uzyskasz w Leanie pisząc `\or`. Zdanie o postaci alternatywy można
-- udowodnić na dokładnie dwa sposoby: albo dostarczając dowód jej lewego członu, albo prawego. A
-- więc bliżej nieokreślony dowód alternatywy jest w pewnym sensie bardziej nieokreślony niż bliżej
-- nieokreślony dowód koniunkcji.

-- Zadanie 2: Uzupełnij dowód, zastępując `sorry` aplikacją (do wiadomo czego) pierwszego z dwóch
-- konstruktorów dowodu alternatywy, to jest konstruktora `Or.inl` ...

example : p → p ∨ q := fun hp : p => sorry

-- ... a następnie, domyślając się, jak nazywa się drugi konstruktor alternatywy, uzupełnij
-- brakujący kod tutaj:

example : q → p ∨ q := sorry

-- Ponieważ wiedząc tylko, że mamy *jakiś* dowód alternatywy, nie wiemy, czy to jest dowód jej
-- lewego członu, czy prawego, to żeby coś wynikało z *samej* alternatywy, musi wynikać z *każdej* z
-- tych dwóch *możliwości*.

-- Zadanie 3: `Or.elim`, czyli implementacja (jedynej) reguły użycia (dowodu) alternatywy, to
-- funkcja (niby tylko pozornie, ale skoro funkcjonalnie, a to jest matematyka, to też jednocześnie
-- "nieporoznie") trójargumentowa. Uzupełnij dowód zastępując `sorry` widocznymi w tym fragmencie
-- kodu hipotetycznymi dowodami implikacji `p → r` i `q → r`:

example : (p → r) → (q → r) → (p ∨ q → r) :=
  fun hpr : p → r =>
    fun hqr : q → r =>
      fun hporq : p ∨ q => Or.elim hporq sorry

-- Mamy tutaj potrójnie zagnieżdżoną funkcję, czyli funkcję, która zwraca funkcję, która zwraca
-- funkcję, bo mamy trzy implikacje do "obsłużenia" za pomocą anonimowych funkcji:
--
-- `(p → r) → ...`, `(q → r) → ...` i `p ∨ q → r`.
--
-- Dlatego, żeby zwiększyć czytelność kodu, zastosowałem wcięcia. Z (hipotetycznych) dowodów
-- implikacji `p → r` i `q → r` tylko korzystamy; nie musimy tych implikacji tutaj udowadniać, bo te
-- dowody mamy dostawać na wejściu tej funkcji.

-- I to jest w zasadzie wszystko, co trzeba wiedzieć o (logicznej) alternatywie.

-- Zadanie 4, dla osób zbyt ambitnych:

example : (p → q) → (¬q → ¬p) := sorry

-- Odrobina pomocy: Żeby udowodnić implikację `(p → q) → (¬q → ¬p)`, której poprzednikiem jest
-- implikacja `(p → q)`, trzeba skonstruować funkcję anonimową, która z dowolnego dowodu
-- zdania/termu typu `(p → q)` będzie robić dowód zdania/term typu `(¬q → ¬p)`. Żeby z kolej
-- udowodnić zdanie `(¬q → ¬p)`, trzeba skonstruować funkcję anonimową, która z dowolnego dowodu
-- zdania `¬q` zrobi dowód zdania `¬p`. A żeby udowodnić zdanie `¬p`, które jest również implikacją,
-- ale do fałszu, trzeba z dowolnego dowodu zdania `p` (sic!) zrobić (czysto hipotetyczny) dowód
-- zdania `False`. Skoro ten ostatni term jest *zawsze* tylko hipotetyczny, to *jedynym* sposobem, w
-- jaki można go (na niby) uzyskać, jest *aplikacja dowodu jakiejś negacji* (będącego funkcją) do
-- dowodu zdania w tej negacji negowanego. Jedynym kandydatem jest tutaj dowód `¬q`. Dowodem
-- twierdzenia-implikacji `(p → q) → (¬q → ¬p)`, którego następnikiem jest tak zwana implikacja
-- przeciwstawna (do implikacji będącej poprzednikiem tego twierdzenia), inaczej kontrapozycja,
-- będzie więc również funkcja potrójnie zagnieżdżona.

----------------------------------------------------------------------------------------------------
-- NALEŻĄ SIĘ GRATULACJE

-- Znasz już podstawy logiki zdań w wersji konstruktywnej i wiesz trochę o programowaniu funkcyjnym,
-- a także o podstawach całej matematyki. Tą wiedzę i te umiejętności możesz odtąd samodzielnie
-- utrwalać i rozwijać korzystając z niezawodności asystenta dowodzenia Lean.
