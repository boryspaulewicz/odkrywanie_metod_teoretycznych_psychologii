----------------------------------------------------------------------------------------------------
-- ALTERNATYWA, NEGACJA I FAŁSZ

variable (p q r : Prop)

-- Implikacja to typ pewnego rodzaju funkcji, to jest takiej, która przekształca dowody jakiegoś
-- zdania w dowody jakiegoś (być może innego) zdania, a skoro to typ funkcji, to również jakiegoś
-- *procesu*. Koniunkcja to typ *statycznej* struktury danych, konkretnie typ uporządkowanych par
-- dowodów zdań. Podobnie jak "zwyczajne" funkcje, implikacje coś "robią", i może właśnie (między
-- innymi) dlatego oznaczamy jedne i drugie za pomocą strzałki. Koniunkcja to bardziej takie bycie
-- razem. W naszej logice prawda również nic nie robi, bo tylko jest, i nie ma wewnętrznej
-- struktury, dlatego można właściwie powiedzieć, że prawda jest (tutaj) byciem lub bytem jako
-- takim.

----------------------------------------------------------------------------------------------------
-- FAŁSZ

-- Istnieje również zdanie ...

#check False -- False : Prop

-- ... które ma tą właściwość, że *nie istnieje dowód tego zdania*. A więc to - raz na zawsze -
-- *tylko* (puste) zdanie.

-- Technicznie, ta własność polega na tym, że `False` jest typem, który z definicji, albo
-- aksjomatycznie, nie posiada konstruktora. Termy mające typ implikacji konstruujemy za pomocą
-- słowa kluczowego `fun`, termy mające typ koniunkcji za pomocą `And.intro`, term typu `True` jest
-- tylko jeden i jest nim konstruktor bezargumentowy `True.intro`, a `False` jest tym, czym jest,
-- właśnie dlatego, że ten typ nie ma konstruktora.

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

-- Skoro Lean nie narzeka, to term `fun hp : p => hp` jest dowodem `p → p`.

-- Można to zapisać jeszcze krócej, bo Lean jest w stanie wywnioskować, jaki typ musi mieć parametr:

example : p → p := fun hp => hp

-- To samo można udowodnić też tak, bo dowód tego twierdzenia to szczególny przypadek funkcji
-- identycznościowej, która (w postaci uogólnionej) nazywa się w Leanie `id`:

example : p → p := id

-- Ale już wróćmy do fałszu. Aksjomatyczną konwencję, że z fałszu wynika wszystko, czyli, że (zawsze
-- tylko hipotetyczny) term typu `False` *mógłby* zostać użyty, żeby udowodnić dowolne zdanie,
-- nazywamy *zasadą eksplozji dedukcyjnej*, a po łacinie ex falso quodlibet. Nie ma w tym chyba nic
-- szczególnie intuicyjnego, może poza tym, że *nie da się wykazać, że nie jest prawdą*, że `False →
-- p`, ponieważ nie da się nigdy wywołać tego typu funkcji i przekonać się w ten sposób, że ta
-- funkcja nie działa, bo żaden term typu `False` nie istnieje i wobec tego nie ma niczego, do czego
-- można by funkcję tego typu aplikować.

----------------------------------------------------------------------------------------------------
-- NEGACJA

-- Negacja to w Leanie tak naprawdę *implikacja* do zdania/typu `False`. Symbol negacji `¬` uzyskasz
-- pisząc `\neg`.

#check ¬p -- ¬p : Prop

-- Jeśli umieścisz kursor nad termem `¬p`, występującym zaraz po komendzie `#check`, to Lean pokaże
-- Ci okno pomocy, w którym wyjaśni, że negacja to właśnie implikacja do fałszu w przebraniu
-- zwięzłej notacji.

-- A skoro z fałszu wynika każde zdanie, negacja zdania to implikacja z tego zdania do fałszu, a
-- implikacja to funkcja, którą można aplikować uzyskując term typu będącego następnikiem tej
-- implikacji, to nie tylko możemy *aplikować negacje*, ale również ze sprzeczności wynika wszystko.
-- Może nie od razu to widać, ale można to udowodnić.

-- Zadanie 1: Zastąp `sorry` aplikacją dowodu/funkcji/termu typu zdaniowego `¬p` do dowodu/termu
-- typu zdaniowego `p`. Musisz tylko wydobyć te (hipotetyczne) dowody z dowodu koniunkcji, którym
-- jest `h`, i zapisać je w odpowiedniej kolejności, tak jak to robiliśmy wcześniej, używając
-- (dowodów) koniunkcji w dowodach. Ponieważ (czysto hipotetyczny) rezultat tej aplikacji ma typ
-- `False`, to wywołanie na rzecz (czysto hipotetycznego) termu tego typu tak zwanej składowej
-- `elim` (to właśnie tutaj robimy) pozwala udowodnić każde zdanie.

example : (p ∧ ¬p) → q := (fun h : (p ∧ ¬p) => (sorry).elim)

-- I to jest wszystko, co trzeba wiedzieć o negacji. Może warto tylko dodać, że z tej perspektywy
-- negacja to niemal dosłownie droga doNikąd i zarazem Pusta obietnica.

-- Widzimy więc, choćbyśmy nawet nie chcieli, że - całkiem dosłownie - w każdej negacji kryje się
-- Fałszywość. A także Absolutny Brak, przez co negacja odpowiada temu, co według św. Tomasza z
-- Akwinu jest samą istotą Grzechu.

-- I jak tu nie popaść w (niekoniecznie teistyczny <i czy aby na pewno taki całkiem pop?>)
-- mistycyzm?

----------------------------------------------------------------------------------------------------
-- ALTERNATYWA

-- Jeżeli koniunkcja to takie jakby bycie razem, albo współbycie, to alternatywa to taki jakby
-- *wybór*, albo *możliwość*, a może nawet wręcz najprostsza postać *niepewności*.

-- Symbol alternatywy `∨` uzyskasz w Leanie pisząc `\or`. Zdanie o postaci alternatywy można
-- udowodnić na dokładnie dwa sposoby: albo dostarczając dowód jej lewego członu, albo prawego. A
-- więc bliżej nieokreślony dowód alternatywy jest w pewnym sensie jeszcze bardziej nieokreślony niż
-- bliżej nieokreślony dowód koniunkcji.

-- Zadanie 2: Uzupełnij dowód zastępując `sorry` aplikacją, do wiadomo czego, pierwszego z dwóch
-- konstruktorów dowodu alternatywy, to jest `Or.inl` ...

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
-- BONUS CONTENT: Po Drugiej Stronie

-- Istnieje pewna głęboka analogia, a właściwie coś *analogicznego do analogii*, między prawdą i
-- koniunkcją z jednej strony, a fałszem i alternatywą z drugiej:

-- Prawda wynika ze wszystkiego. Z fałszu wynika wszystko.

-- Istnieje dokładnie jeden sposób udowodnienia prawdy i nie istnieje żaden sposób udowodnienia
-- fałszu. W tym sensie prawda jest jak liczba `1`, a fałsz jest jak liczba `0`.

-- Istnieje dokładnie jeden sposób udowodnienia koniunkcji i dokładnie dwa sposoby użycia koniunkcji
-- w dowodzie. Istnieją dokładnie dwa sposoby udowodnienia alternatywy i dokładnie jeden sposób
-- użycia alternatywy w dowodzie.

-- Korzystając z *koniunkcji* w dowodzie korzystamy *albo* z jej lewego członu, *albo* prawego,
-- *albo z odywdu* członów. W ten sposób *pojęcie* logicznej altarnatywy pojawia się w *sposobie
-- korzystania* z koniunkcji.

-- Korzystając z alternatywy w dowodzie korzystamy *zarówno* z wynikania czegoś z jej lewego członu
-- jak i z prawego. W ten sposób *pojęcie* logicznej koniunkcji pojawia się w *sposobie korzystania*
-- z alternatywy.

-- `∧` to symbol taki sam jak `∨`, tyle, że odwrócony do góry nogami.

-- Jak łatwo wykazać (jeżeli nie będziesz panikować, to na pewno poradzisz sobie z tym niebawem bez
-- trudu, o ile już nie wiesz, jak te zdania można udowodnić), dla każdego zdania `p`, ...
--
--  `True ∧ p → p` i `p ∧ True → p` i `p → True ∧ p` i `p → p ∧ True`,
--
-- ... a zatem `True ∧ p ↔ p` i `p ∧ True ↔ p` (symbol równoważności `↔` uzyskasz pisząc `\iff`).
-- Jeżeli więc `∧` jest jak mnożenie (a tak się składa, że faktycznie jest), to `True` jest jak
-- liczba `1` *również* w tym znaczeniu, że jest *elementem neutralnym*, czyli takim jakby
-- "znikającym w użyciu", ze względu na *operację binarną* (akurat tutaj na zdaniach, a nie na
-- liczbach), którą oznaczamy w logice za pomocą symbolu `∧`. Tak samo jak dla każdej liczby `x`, `1
-- × x = x × 1 = x`. Analogiczna sytuacja występuje w przypadku logicznej alternatywy, fałszu,
-- dodawania i zera.

-- (Może masz ochotę spróbować udowodnić którąś z tych ostatnich implikacji <nie chodzi mi o
-- równoważności>?)

-- Co więcej, w pewnym (bardzo abstrakcyjnym) sensie dodawanie i mnożenie, a więc również koniunkcja
-- i alternatywa, to *jedna i ta sama operacja*, tylko "działająca" *dualnie*. Zresztą `1` i `0` to
-- też obiekty dualne, czyli (wcale nie tak metaforycznie, jak się może wydawać) wzajemne lustrzane
-- odbicia. Można się z faktem, że dodawanie i mnożenie to w zasadzie to samo, zapoznać wstępnie
-- przypominając sobie, że dodawanie staje się mnożeniem, gdy zastosujemy do niego funkcję
-- wykładniczą, a mnożenie staje się dodawaniem, gdy zastosujemy do niego logarytm, i te dwie
-- funkcje są względem siebie odwrotne, a więc są również w pewnym sensie jedną i tą samą funkcją,
-- tyle, że "działającą" raz w jedną, a raz w drugą stronę.

-- No dobrze, a co z implikacją? Cieszę się, że pytasz. Otóż implikacja jest w pewnym technicznym i
-- ekstremalnie abstrakcyjnym sensie w zasadzie tym samym, co funkcja wykładnicza! I to ma ścisły
-- związek z curryingiem! A wszystko to jest, przynajmniej moim zdaniem, jednocześnie odrażająco
-- piękne i szalenie praktyczne.

----------------------------------------------------------------------------------------------------
-- NALEŻĄ SIĘ GRATULACJE

-- Znasz już podstawy logiki zdań w wersji konstruktywnej i wiesz trochę o programowaniu funkcyjnym,
-- a także o podstawach całej matematyki. Tą wiedzę i te umiejętności możesz odtąd samodzielnie
-- utrwalać i rozwijać korzystając z niezawodności asystenta dowodzenia Lean.

----------------------------------------------------------------------------------------------------
-- PS(ST)

-- Byłbym zapomniał - `p ↔ q` to z definicji to samo, co `(p → q) ∧ (q → p)`, ale udowadniamy
-- równoważność raczej korzystając z (oczywiście dwuargumentowego) konstruktora `Iff.intro`. No to
-- może udowodnij jeszcze, zastępując `sorry` dowodami zdań `q ∧ p` i `p ∧ q`, poniższe twierdzenie,
-- które mówi, że (podobnie jak mnożenie liczb) logiczna koniunkcja jest *działaniem przemiennym*
-- (na zdaniach). Trzeba tam tylko zastosować dwa razy `And.intro`, bo co innego, za każdym razem
-- podając jako argumenty dowody prawego i lewego (w *tej* kolejności) członu koniunkcji, której
-- dowód jest w danym miejscu w kodzie widoczny.

example : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro (fun hpq : p ∧ q => sorry) (fun hqp : q ∧ p => sorry)

----------------------------------------------------------------------------------------------------
-- SP

-- Skoro z fałszu wynika każde zdanie, a prawda wynika z każdego zdania, to musi być tak, że:

example : False → True := fun hF => sorry

-- Istnieje dokładnie jedna funkcja (matematyczna albo funkcja jako program) ze zbioru pustego,
-- czyli zera, do (każdego) zbioru jednoelementowego, czyli (funkcjonalnie) jedynki.

-- O obiektach, które "emitują" w pewien bardzo abstrakcyjny sposób rozumiane unikalne "strzałki"
-- *do* każdego obiektu (tego samego rodzaju) mówimy też w matematyce, że to obiekty początkowe albo
-- początki. Z kolei o obiektach, które "otrzymują" w ten sam sposób rozumiane unikalne strzałki
-- *od* każdego obiektu mówimy, że to obiekty końcowe. Między innymi zbiór pusty, zero i typ `False`
-- to obiekty początkowe, a między innymi (każdy) zbiór jednoelementowy, jedynka i typ `True` to
-- obiekty końcowe. Obiekt początkowy i obiekt końcowy to struktury względem siebie dualne, czyli
-- dokładnie (w pewnym bardzo abstrakcyjnym sensie) swoje lustrzane odbicia.

-- Wyobraź sobie teraz wszystkie możliwe *formuły logiczne*, to znaczy formalne zdania, które są
-- albo zdaniami *atomowymi*, takimi jak `False`, `True` i `p` czy `q`, albo koniunkcjami,
-- alternatywami, implikacjami, lub negacjami zdań *niekoniecznie* atomowych. Tak rozumianych zdań
-- jest nieskończenie wiele, bo, dajmy na to, `p ∧ p` jest takim zdaniem, a wobec tego również `(p ∧
-- p) ∧ p` jest zdaniem, i tak dalej. Wyobraź sobie też, że od każdego zdania wychodzą strzałki -
-- ale może inaczej rysowane, bo mają oznaczać coś innego niż implikację - do każdego takiego
-- zdania, które z tego pierwszego w *jakikolwiek* sposób logicznie wynika. To znaczy, że każda taka
-- strzałka reprezentuje *relację dowiedlności*, a nie żaden *konkretny* dowód. W szczególności,
-- każda koniunkcja emituje między innymi dwie takie strzałki, do zdań będących jej członami, i
-- każda alternatywa dostaje między innymi dwie takie strzałki, od zdań będących jej członami.
-- Zdanie `False` emituje *dokładnie jedną* taką strzałkę do każdego zdania, w tym również do zdania
-- `False`, i każde zdanie, w tym również `True`, emituje dokładnie jedną taką strzałkę do zdania
-- `True`.

-- W naszej logice jest zatem nie tylko prawdą, że Fałsz istnieje co najwyżej tylko z nazwy albo
-- pozornie, ale w dodatku *wszystkie* drogi prowadzą ostatecznie do Prawdy. Żeby tą Prawdę
-- "osiągnąć", nie trzeba się jednak wcale ruszać z miejsca, bo Ona zawsze po prostu jest
-- (natychmiast dostępna); w dodatku jako coś, co jest zarazem najważniejsze i w pewnym sensie
-- najmniej interesujące. Już nie tak ważne, ale za to najbardziej interesujące są *strzałki ze
-- zdania `True`*, czyli *wskazane miejsca*, do których można *faktycznie skądś dojść*, bo *te*
-- strzałki odpowiadają dokładnie wszystkim *zdaniom nietrywialnie prawdziwym*, to jest *nieatomowym
-- twierdzeniom*.

-- Funkcje matematyczne można rozumieć jako formalne odpowiedniki *oznaczania*, bo to są *arbitralne
-- przyporządkowania* każdemu elementowi jednego zbioru, nazywanego dziedziną funkcji, dokładnie
-- jednego elementu drugiego zbioru, nazywanego jej przeciwdziedziną. Przeciwdziedzina to z tej
-- perspektywy kontekst, a dziedzina to taki maksymalnie ubogi język, w którym są tylko nazwy
-- własne. Każda funkcja może być więc rozumiana jako jednoczesne nazywanie czy wręcz wskazywanie (i
-- może <również> stąd ta strzałka?) jakiś rzeczy w jakimś kontekście (albo w jakiejś "sytuacji").

-- Jeżeli tak, to czym jest - istniejąca unikalnie! - funkcja ze zbioru pustego do zbioru
-- jednoelementowego? Nazywaniem czegoś, będącego całością jakiegoś kontekstu? Ale przecież,
-- ponieważ dziedzina tej funkcji jest zbiorem pustym, nie ma tu nawet najuboższego możliwego
-- języka. Czy wobec tego nie można powiedzieć, że taka funkcja jest *przedjęzykowym oznaczaniem*,
-- czyli *zwracaniem uwagi* na to, co jest, jako na pewną całość?

-- I czy zwracanie uwagi nie jest najbardziej fundamentalnym aktem *oceny*? Bo zwracać na coś
-- u-wagę, to traktować to coś, choćby na chwilę, jako w jakiś sposób przynajmniej potencjalnie
-- ważne. W niechęci czy nienawiści jest zawsze pewien elementarny szacunek, bo jeśli coś budzi w
-- nas niechęć, nienawiść, czy wstręt, to musi być tak, że to coś się dla nas *liczy*. Nie da się,
-- przynajmniej w pewnym sensie, bardziej negatywnie ocenić czegoś, niż jako coś nieistotnego.

-- Jak ujęła to pewna łobuziara: L'attention est la forme la plus rare et la plus pure de la
-- générosité.

-- I czy nie jest też tak, że - ponieważ, kiedy jesteśmy przytomni, działa mechanizm projekcji -
-- najłatwiej jest nam odkryć stan własnego umysłu przyglądając się temu, jak nam się jawi
-- "zewnętrzny" świat (szczególnie zaś "inni" ludzie)? Bo introspekcja wychodzi nam raczej
-- tak sobie. Czy świat taki, jakim nam się w danym momencie jawi - czyli świat-w-swoim-istnieniu,
-- bo przecież przeszłego świata już nie ma, a przyszłego jeszcze nie ma - nie jest wobec tego w
-- jakiś sposób naszym najwierniejszym lustrem, pokazującym nam naszą najbardziej subiektywną i
-- podstawową (i może nawet przedosobową) "postać" albo ... Postawę?

-- Wydaje się więc, że ustaliliśmy jak dotąd, że Fałsz to jednocześnie Zero, Pustka albo Absolutny
-- Brak inaczej Grzech, i lustrzane odbicie Istnienia, Jedności i Prawdy.

-- Chyba już pora na coś bardziej odklejonego, czyli przyziemnego.

----------------------------------------------------------------------------------------------------
-- NAJWYRAŹNIEJ DOPUSZCZALNE (?) INTERPRETACJE LOGICZNEJ RELACJI MIĘDZY FAŁSZEM I PRAWDĄ

-- Logiczna relacja między Fałszem i Prawdą to Ocena albo Owoc z Drzewa Poznania (Dobrego i Złego),

-- to Sama Uwaga,

-- to Coś, czego istotą jest Aktywne->Niebycie->Wobec->Istnienia,

-- albo sam Początek Ruchu, z Niebytu do Bytu, albo z Ciemności do Światła.

-- *Wygląda* więc na to, że To właśnie jest Klejnot w Lotosie! ॐ मणि पद्मे हूँ!

-- Albo, jak ujął to pewien łobuz: Soll Gott gesehen werden... mein Auge und Gottes Auge ist ein
-- Auge und ein Erkennen und ein Lieben.

-- I czy to nie są wszystko w istocie sprawy Psycho-Logiczne?

-- To już może I=Will See-My-Self-Out 😘

----------------------------------------------------------------------------------------------------
-- BTW, Q.E.D. (FR, chyba, że znajdziesz kontrargument)

-- Zadanie 5: Tym razem zamiast *udowadniać*, że jakieś *zdanie* jest albo nie jest *prawdziwe*,
-- spróbuj *zademonstrować*, że któraś z przytoczonych *interpretacji* jest *nieadekwatna* lub
-- *bezużyteczna*.
--
-- Dlaczego i po co? Może na przykład dlatego, że w psychologii - nie tylko w kontekście terapii -
-- interpretacje odgrywają niezwykle doniosłą rolę? I po to, żeby zarówno same te interpretacje, jak
-- i to, czego dotyczą, trochę lepiej w ten sposób zrozumieć? Ale uwaga: *nie każda* niespójność
-- albo paradoks prowadzi do *bezużyteczności*! (patrz hasło "logika parakonsystentna").

-- Można powiedzieć, że czasem "naginam" tu język, ale czy faktycznie? Jeżeli jakąś perspektywę da
-- się konsekwentnie przyjmować, to ta perspektywa po prostu jest i raczej nic się w niej nie
-- wygina. *Zmiana* perspektywy, tak ważna między innymi w procesie terapii, to co innego - wtedy
-- Coś się faktycznie *rusza*, ale właściwie co? Czy może raczej Kto? Kim jest ów Ten, który
-- istnieje jeszcze zanim przyjmie jakąś perspektywę? Czy ten Ktoś to nie jest przypadkiem, wydaje
-- się wręcz, że z jakiejś trudnej do uchwycenia definicji - we Własnej Osobie - sam Widok Znikąd?

-- Na koniec wypada wspomnieć, że (może niespodziewanymi) bohaterami tego odcinka byli między innymi
-- - poza wspomnianym już Tomkiem - (w mojej ocenie wybitni psycho-logowie) Simone Weil, Mistrz
--   Eckhart, Budda i Thomas Nagel.
