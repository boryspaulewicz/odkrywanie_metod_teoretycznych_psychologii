----------------------------------------------------------------------------------------------------
-- PO dRUGIEJ sTRONIE

-- Istnieje pewna głęboka analogia, a właściwie coś *analogicznego do analogii*, między prawdą i
-- koniunkcją z jednej strony, a fałszem i alternatywą z drugiej:

-- Prawda wynika ze wszystkiego. Z fałszu wynika wszystko.

-- Istnieje dokładnie jeden sposób udowodnienia prawdy i nie istnieje żaden sposób udowodnienia
-- fałszu. W tym sensie prawda jest jak liczba `1`, a fałsz jest jak liczba `0`.

-- Istnieje dokładnie jeden sposób udowodnienia koniunkcji i istnieją dokładnie dwa sposoby użycia
-- koniunkcji w dowodzie. Istnieją dokładnie dwa sposoby udowodnienia alternatywy i dokładnie jeden
-- sposób użycia alternatywy w dowodzie.

-- Korzystając z *koniunkcji* w dowodzie korzystamy *albo* z jej lewego członu, *albo* prawego,
-- *albo z odywdu* członów. W ten sposób *pojęcie* logicznej altarnatywy pojawia się w *sposobie
-- korzystania* z koniunkcji.

-- Korzystając z alternatywy w dowodzie korzystamy *zarówno* z wynikania czegoś z jej lewego członu,
-- jak i z prawego. W ten sposób *pojęcie* logicznej koniunkcji pojawia się w *sposobie korzystania*
-- z alternatywy.

-- `∧` to symbol taki sam jak `∨`, tyle, że odwrócony do góry nogami.

-- Jak łatwo wykazać (jeżeli nie będziesz panikować, to na pewno poradzisz sobie z tym niebawem bez
-- trudu, o ile już nie wiesz, jak te zdania można udowodnić), dla każdego zdania `p`, ...
--
--  `True ∧ p → p` i `p ∧ True → p` i `p → True ∧ p` i `p → p ∧ True`,
--
-- ... a zatem `True ∧ p ↔ p` i `p ∧ True ↔ p` (symbol równoważności `↔` uzyskasz pisząc `\iff`).
--
-- Jeżeli więc `∧` jest jak mnożenie (a faktycznie jest), to `True` jest jak liczba `1` *również* w
-- tym znaczeniu, że jest *elementem neutralnym*, czyli "znikającym w użyciu", ze względu na
-- *operację binarną* (akurat tutaj na zdaniach, a nie na liczbach), którą oznaczamy w logice za
-- pomocą symbolu `∧`:

-- *Dla każdego* zdania `p`, `True ∧ p ↔ p ↔ p ∧ True`.
--
-- Dla każdej liczby `x`,       `1 × x = x = x × 1`.

-- Analogiczna sytuacja występuje w przypadku logicznej alternatywy, fałszu, dodawania i zera.

-- (Może masz ochotę spróbować udowodnić którąś z ostatnich implikacji <nie chodzi o
-- równoważności>?)

-- Co więcej, w pewnym (bardzo abstrakcyjnym) sensie dodawanie i mnożenie, a więc również koniunkcja
-- i alternatywa, to *jedna i ta sama operacja*, tylko "działająca" *dualnie*. Zresztą `1` i `0` to
-- też obiekty dualne, czyli (wcale nie tak metaforycznie, jak się może wydawać) wzajemne lustrzane
-- odbicia, a więc *ten sam obiekt oglądany z dwóch stron*.
--
-- Z faktem, że dodawanie i mnożenie to w zasadzie to samo, można się wstępnie zapoznać
-- przypominając sobie, że dodawanie staje się mnożeniem, gdy zastosujemy do niego funkcję
-- wykładniczą, a mnożenie staje się dodawaniem, gdy zastosujemy do niego logarytm, i te dwie
-- funkcje są względem siebie odwrotne, więc są również w pewnym sensie jedną i tą samą funkcją,
-- tyle, że "działającą" raz w jedną, a raz w drugą stronę.

-- No dobrze, a co z implikacją? Cieszę się, że pytasz. Otóż implikacja jest w pewnym technicznym i
-- (ekstremalnie) abstrakcyjnym sensie w zasadzie tym samym, co funkcja wykładnicza! I to ma ścisły
-- związek z curryingiem! A wszystko to jest, przynajmniej moim zdaniem, odrażająco piękne a także
-- szalenie praktyczne.

----------------------------------------------------------------------------------------------------
-- RÓWNOWAŻNOŚĆ TO KONIUNKCJA TEJ SAMEJ IMPLIKACJI W DWIE STRONY

-- Zdanie o postaci `p ↔ q` to z definicji to samo, co `(p → q) ∧ (q → p)`, ale udowadniamy
-- równoważność raczej korzystając z (dwuargumentowego) konstruktora `Iff.intro`, a nie z
-- `And.intro`.

-- Zadanie 1: Udowodnij, zastępując `sorry` dowodami zdań `q ∧ p` i `p ∧ q`, twierdzenie, które
-- mówi, że (podobnie jak mnożenie liczb) logiczna koniunkcja jest *działaniem przemiennym* (na
-- zdaniach). Trzeba tam tylko zastosować dwa razy `And.intro`, bo co innego, za każdym razem
-- podając jako argumenty dowody prawego i lewego (w *tej* kolejności) członu koniunkcji, której
-- (hipotetyczny) dowód jest w danym miejscu widoczny.

example : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro (fun hpq : p ∧ q => sorry) (fun hqp : q ∧ p => sorry)

----------------------------------------------------------------------------------------------------
-- RELACJA MIĘDZY FAŁSZEM I PRAWDĄ

-- Skoro z fałszu wynika każde zdanie, a prawda wynika z każdego zdania, to musi być tak, że:

example : False → True := fun hF => sorry

-- Żeby istniała funkcja z jednego zbioru do drugiego, *każdy* element pierwszego zbioru musi mieć
-- dokładnie *jeden* odpowiednik w drugim zbiorze. Istnieje dokładnie jedna, czyli unikalna funkcja
-- (matematyczna albo funkcja jako program) ze zbioru pustego, czyli zera, do (każdego) zbioru
-- jednoelementowego, czyli (funkcjonalnie) jedynki, z dwóch niezależnych powodów. Po pierwsze,
-- istnieje tylko jeden (pusty) sposób, żeby każdemu elementowi zbioru pustego przypisać unikalny
-- element *jakiegokolwiek* zbioru, więc już sam fakt, że dziedzina jest pusta, gwarantuje
-- unikalność tej funkcji. Podobnie sam fakt, że przeciwdziedzina jest zbiorem jednoelementowym,
-- gwarantuje unikalność funkcji do tego zbioru z każdego zbioru, bo wszystkie elementy dziedziny,
-- jaka by ona nie była, muszą być posłane do jedynego elementu przeciwdziedziny.

-- O obiektach, które emitują w pewien (bardzo) abstrakcyjny sposób rozumiane unikalne strzałki *do*
-- każdego obiektu (tego samego rodzaju) mówimy też w matematyce, że to obiekty początkowe albo
-- początki. Z kolei o obiektach, które otrzymują w ten sam sposób rozumiane unikalne strzałki *od*
-- każdego obiektu mówimy, że to obiekty końcowe. Między innymi zbiór pusty, zero i typ `False` to
-- obiekty początkowe, a między innymi (każdy) zbiór jednoelementowy, jedynka i typ `True` to
-- obiekty końcowe. Z tych definicji wynika, że jeśli w jakimś "matematycznym świecie" istnieją
-- obiekt początkowy (`I`) i końcowy (`T`), to istnieje (tak rozumiana) unikalna strzałka ─ `I → T`
-- ─ od pierwszego do drugiego.

-- *Jedyna* różnica między definicjami obiektu początkowego i końcowego dotyczy *kierunku*
-- (wszystkich) strzałek. Właśnie w tym technicznym znaczeniu to są struktury względem siebie
-- dualne, czyli dokładnie swoje lustrzane odbicia.

-- Wyobraź sobie teraz wszystkie możliwe *formuły logiczne*, to znaczy formalne zdania, które są
-- albo zdaniami *atomowymi*, takimi jak `False`, `True` i `p` czy `q`, albo *formułami złożonymi*,
-- to znaczy koniunkcjami, alternatywami, implikacjami, lub negacjami zdań *niekoniecznie*
-- atomowych.
--
-- Tak rozumianych zdań jest nieskończenie wiele, bo, dajmy na to, `p ∧ p` jest takim zdaniem, a
-- wobec tego również `(p ∧ p) ∧ p` jest zdaniem, i tak dalej. Wyobraź sobie też, że od każdego
-- zdania wychodzą strzałki (ale może inaczej rysowane, bo mają oznaczać coś innego niż implikację)
-- do każdego takiego zdania, które z tego pierwszego w *jakikolwiek* sposób logicznie wynika. To
-- znaczy, że każda taka strzałka reprezentuje *relację dowiedlności*, czyli sam *fakt* istnienia
-- dowodu, a nie żaden *konkretny* dowód. To taka różnica jak ta między *istnieniem jakiegoś
-- połączenia* i *konkretnymi drogami* między dwoma punktami na mapie.

-- W szczególności, każda koniunkcja emituje między innymi dwie takie strzałki do zdań będących jej
-- członami, i każda alternatywa dostaje między innymi dwie takie strzałki od zdań będących jej
-- członami. Zdanie `False` emituje dokładnie jedną taką strzałkę do każdego zdania, w tym również
-- do siebie, i każde zdanie, w tym również `True`, emituje dokładnie jedną taką strzałkę do zdania
-- `True`.

-- W naszej logice jest zatem nie tylko prawdą, że Fałsz istnieje co najwyżej tylko z nazwy albo
-- pozornie, ale w dodatku *wszystkie* drogi prowadzą ostatecznie do Prawdy. Żeby tą Prawdę
-- "osiągnąć", nie trzeba się jednak wcale ruszać z miejsca, bo Ona zawsze po prostu jest
-- (natychmiast dostępna); w dodatku jako coś, co jest zarazem najważniejsze i w pewnym sensie
-- najmniej interesujące. Może już nie tak ważne, ale za to niewątpliwie interesujące są *strzałki
-- ze zdania `True`*, czyli *wskazane miejsca*, do których można *faktycznie skądś dojść* (w istocie
-- nigdzie się nie ruszając), bo *te* strzałki odpowiadają dokładnie wszystkim *zdaniom
-- nietrywialnie prawdziwym*, to jest *nieatomowym twierdzeniom*, takim jak `p → p`.
--
-- Żeby zobaczyć, że takie strzałki ze zdania `True` odpowiadają dokładnie twierdzeniom logiki,
-- wystarczy zdać sobie sprawę, że dowód zdania `True` jest jednocześnie ważny i bezużyteczny!

----------------------------------------------------------------------------------------------------
-- CZY TO NA PEWNO "PSYCHOLOGIZOWANIE"?

-- Funkcje matematyczne można rozumieć jako formalne odpowiedniki *oznaczania*, bo to po pierwsze
-- pewne (abstrakcyjne) *pojęcia*, a po drugie to *arbitralne przyporządkowania* ─ każdemu
-- elementowi jednego zbioru, nazywanego dziedziną funkcji, dokładnie jednego elementu drugiego
-- zbioru, nazywanego jej przeciwdziedziną. Przeciwdziedzina to z tej perspektywy kontekst, a
-- dziedzina to taki maksymalnie ubogi język, w którym są tylko nazwy własne. Dlatego funkcje
-- nazywamy w matematyce też "mapami" albo "mapowaniami" czy wreszcie "odwzorowaniami". Każda
-- funkcja może być więc rozumiana jako jednoczesne nazywanie czy wręcz wskazywanie (i może
-- <również> stąd ta strzałka?) jakiś "rzeczy", "miejsc" albo "własności" w jakimś kontekście (albo
-- w jakiejś "sytuacji").

-- Jeżeli tak, to *czym* jest, istniejąca unikalnie, funkcja ze zbioru *pustego* do zbioru
-- *jednoelementowego*? Nazywaniem czegoś, będącego *całością* jakiegoś kontekstu, skoro jej
-- przeciwdziedzina to tylko jedno jakieś coś? Ale przecież, ponieważ dziedzina tej funkcji jest
-- zbiorem pustym, nie ma tu nawet najuboższego możliwego "języka". Czy wobec tego nie można
-- powiedzieć, że taka funkcja jest *przedjęzykowym oznaczaniem*, czyli *zwracaniem uwagi* na to, co
-- *jest*, jako na pewną *całość*?

-- I czy zwracanie uwagi nie jest najbardziej fundamentalnym aktem *oceny*? Bo zwracać na coś
-- u-wagę, to traktować to coś, choćby na chwilę, jako w jakiś sposób przynajmniej potencjalnie
-- ważne. W niechęci czy nienawiści jest zawsze pewien elementarny szacunek, bo jeśli coś budzi w
-- nas niechęć, nienawiść, czy wstręt, to musi być tak, że to coś się dla nas *liczy*. Nie da się,
-- przynajmniej w pewnym sensie, bardziej negatywnie ocenić czegoś, a zwłaszcza kogoś, niż jako coś
-- nieistotnego.
--
-- Jak ujęła to pewna łobuziara: L'attention est la forme la plus rare et la plus pure de la
-- générosité.

-- I czy nie jest też tak, że ─ ponieważ, kiedy jesteśmy przytomni, działa mechanizm projekcji ─
-- najłatwiej jest nam odkrywać aktualny stan własnego umysłu, przyglądając się temu, jak nam się
-- jawi "zewnętrzny" świat (szczególnie zaś "inni" ludzie)? Bo introspekcja wychodzi nam raczej tak
-- sobie. Czy świat taki, jakim nam się w danym momencie jawi ─ czyli świat-w-swoim-istnieniu, bo
-- przecież (za każdym razem) przeszłego świata już nie ma, a przyszłego jeszcze nie ma ─ nie jest
-- wobec tego w jakiś sposób naszym najwierniejszym lustrem, pokazującym nam naszą najbardziej
-- subiektywną i podstawową (i może nawet przedosobową) "postać" albo ... Postawę?

-- Wydaje się więc, że ustaliliśmy jak dotąd, że Fałsz to jednocześnie Zero, Pustka albo Absolutny
-- Brak inaczej Grzech, i lustrzane odbicie Istnienia, Jedności i Prawdy.

-- Chyba już pora na coś bardziej odklejonego, czyli przyziemnego.

----------------------------------------------------------------------------------------------------
-- NAJWYRAŹNIEJ DOPUSZCZALNE (?) INTERPRETACJE LOGICZNEJ RELACJI MIĘDZY FAŁSZEM I PRAWDĄ
--
--              - Co to jest pion? - pyta Jade.
--              - Przeciwieństwo poziomu, idiotko - wyjaśnia Min.
--
--                                                        (George Sounders, *Morszczyn*)


-- Logiczna relacja między Fałszem i Prawdą to Ocena albo Owoc z Drzewa Poznania (Dobrego i Złego),

-- to Sama Uwaga,

-- to Coś, czego istotą jest Aktywne->Niebycie->Wobec->Istnienia,

-- albo sam Początek Ruchu, z Niebytu do Bytu, albo z Ciemności do Światła.

-- *Wygląda* więc na to, że To właśnie jest Klejnot w Lotosie!

-- ॐ मणि पद्मे हूँ

-- أنا الحق

-- Albo, jak ujął to pewien łobuz: Soll Gott gesehen werden... mein Auge und Gottes Auge ist ein
-- Auge und ein Erkennen und ein Lieben.

-- I czy to wszystko nie są w istocie sprawy Psycho-Logiczne?

-- A z innej beczki, co powiesz na taką oto dualność, która według niektórych wynika w dodatku z
-- dualizmu: Dwa zdecydowanie najczęściej występujące rodzaje zaburzeń psychicznych to zaburzenia
-- lękowe i depresyjne. Jedno lub drugie występuje tak często, że niektórzy nazywają je psychicznym
-- przeziębieniem. Jak zasugerował rzekomo jeszcze inny łobuz, istotą depresji jest życie
-- *przeszłością*, a istotą nadmiernego lęku jest życie *przyszłością*. Trudno powiedzieć, czy zaraz
-- "istotą", ale może na chwilę "wychodźmy z tego założenia".

-- Z tej perspektywy w obydwu przypadkach chodzi o *życie czymś, czego nie ma*. Tak jakby strzałka
-- aktywności była skierowana od tego, co jest, do tego, czego nie ma. Wspólną istotą obydwu
-- rodzajów zaburzeń jest jednocześnie negatywna perspektywa albo nastawienie, a mówiąc dokładniej
-- *negatywne złudzenie ocenne*, bo gdyby w tym ocenianiu nie było daleko idącej przesady, nie
-- mielibyśmy do czynienia z zaburzeniami. Czyli w obydwu przypadkach mamy pewną postać fałszu. A
-- najgłębsza *różnica* między tymi zaburzeniami wydaje się (z tej perspektywy) dotyczyć zwrotu
-- *strzałki czasu*. Czyli to też są, przynajmniej w tym znaczeniu, swoje lustrzane odbicia.

-- Pobawmy się też może przy okazji zagadką świadomości. Psychologowie od dawna próbują to coś
-- badać, ale, o ile mi wiadomo, jak dotąd nie udało się ustalić na ten temat nawet *jednego*
-- nietrywialnego faktu. Kiedy słyszymy takie próby wyjaśnienia, jak to, że "jest coś takiego *jak*
-- bycie nietoperzem", to chodzi, wydaje się, o pewną *jakość* pewnego *sposobu doświadczania*, a
-- nie o świadome doświadcz*anie* *jako takie*. Świadomość to zdecydowanie nie punkt za naszymi
-- oczami, w którym skupiają się promienie światła wpadające do naszej głowy. Ani to nie jest żadna
-- przestrzeń albo ekran, w której pojawiają się doświadczenia, bo *przestrzenność* to własność albo
-- część *treści* świadomego doświadczenia. Swiadomość nie jest obiektem materialnym, nie może więc
-- być zlokalizowana w przestrzeni; to przestrzeń, a raczej jej wrażenie, i materialność albo
-- wrażenie substancjalności (związane oczywiście z doświadczaniem dotykowym) są czymś "*w*"
-- świadomości. W ogóle wszystko, co dla nas istnieje, istnieje *z pewnością* *tylko* *w* naszej
-- świadomości.

-- Z tej perpektywy świadomość *jako taka* nie ma właściwości; świadomość tylko *jest* i *tylko* o
-- niej możemy naprawdę wiedzieć, że jest, co czyni ją jednocześnie *pustą* i maksymalnie
-- *obiektywną*. Właściwie nie ma nawet żadnego punktu, *z którego* dopiero coś widzimy, są tylko
-- *widzenia* w różnych "modalnościach" i punkty, które można odnaleźć *dzięki tym widzeniom*, w
-- dostępnych *w ramach* tych widzeń (w takim lub innym sensie) przestrzennych treściach.

-- To już może I=Will See-My-Self-Out 😘

----------------------------------------------------------------------------------------------------
-- BTW, Q.E.D. (FR, chyba, że znajdziesz kontrargument)

-- Zadanie 5: Tym razem zamiast *udowadniać*, że jakieś *zdanie* jest albo nie jest *prawdziwe*,
-- spróbuj *zademonstrować*, że któraś z przytoczonych *interpretacji* jest *nieadekwatna* lub
-- *bezużyteczna*.
--
-- Dlaczego i po co? Może na przykład dlatego, że w psychologii ─ nie tylko w kontekście terapii ─
-- interpretacje odgrywają niezwykle doniosłą rolę? I po to, żeby zarówno same te interpretacje, jak
-- i to, czego dotyczą, trochę lepiej w ten sposób zrozumieć? Ale uwaga: *nie każda* niespójność
-- albo paradoks prowadzi do bezużyteczności! (patrz hasło "logika parakonsystentna", albo
-- przypomnij sobie, co zmarła niedawno wspaniała Marsha Linehan mówiła o roli *dialektyki* w
-- procesie terapii).

-- Można powiedzieć, że czasem "naginam" tu język, ale czy faktycznie? Jeżeli jakąś perspektywę da
-- się konsekwentnie przyjmować, to ta perspektywa po prostu jest i raczej nic się w niej nie zgina.
-- *Zmiana* perspektywy, tak ważna między innymi w procesie terapii, albo gdy próbujemy coś
-- teoretycznie wyjaśniać czy głębiej zrozumieć, to co innego ─ wtedy Coś się faktycznie *rusza*,
-- ale właściwie co? Czy może raczej Kto? Kim jest ten Ów, który istnieje jeszcze zanim przyjmie
-- jakąś perspektywę? Czy ten jakiś Ktoś, to nie przypadkiem, wydaje się wręcz, że z trudnej do
-- uchwycenia definicji ─ we Własnej Osobie ─ sam Widok Znikąd?

-- Na koniec wypada wspomnieć, że (może niespodziewanymi) niejawnymi bohaterami tego odcinka byli
-- między innymi ─ w mojej ocenie wybitni Psycho-Logowie ─ Simone Weil, Al-Halladż, Mistrz Eckhart,
-- Ten, który Obudził się na jawie, Ten, który został Namaszczony, Arthur Schopenhauer i Thomas
-- Nagel 🫥
