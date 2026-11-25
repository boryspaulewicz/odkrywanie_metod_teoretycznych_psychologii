----------------------------------------------------------------------------------------------------
-- PO dRUGIEJ sTRONIE

/-
(Komentarze ciągnące się przez wiele linii wystarczy otoczyć symbolami `/-` i `-/`)

Istnieje pewna głęboka analogia, a raczej coś *analogicznego do analogii*, między prawdą i
koniunkcją z jednej strony, a fałszem i alternatywą z drugiej:

- Prawda wynika ze wszystkiego. Z fałszu wynika wszystko.

- Istnieje dokładnie jeden (kanoniczny) sposób udowodnienia prawdy i nie istnieje żaden sposób udowodnienia
fałszu. W tym, ale nie tylko w tym sensie prawda jest jak liczba `1`, a fałsz jest jak liczba `0`.

- Istnieje dokładnie jeden (kanoniczny) sposób udowodnienia koniunkcji i istnieją dokładnie dwa sposoby użycia
koniunkcji w dowodzie. Istnieją dokładnie dwa sposoby udowodnienia alternatywy i dokładnie jeden
sposób użycia alternatywy w dowodzie.

- Używając w dowodzie *koniunkcji* , korzystamy *albo* z jej lewego członu, *albo* prawego, *albo* z
odywdu. W ten sposób *pojęcie* logicznej altarnatywy pojawia się w *sposobie korzystania*
z koniunkcji.

- Używając w dowodzie *alternatywy*, korzystamy *zarówno* z wynikania czegoś z jej lewego członu,
jak i z prawego. W ten sposób *pojęcie* logicznej koniunkcji pojawia się w *sposobie korzystania*
z alternatywy.

- `∧` to symbol taki sam jak `∨`, tyle, że odwrócony do góry nogami.

- Jak łatwo wykazać (jeżeli nie będziesz panikować, na pewno poradzisz sobie z tym niebawem bez
  trudu, o ile już nie wiesz, jak te zdania można udowodnić), dla każdego zdania `p`, ...

`True ∧ p → p` i `p ∧ True → p` i `p → True ∧ p` i `p → p ∧ True`,

... a zatem `True ∧ p ↔ p` i `p ∧ True ↔ p` (symbol równoważności `↔` uzyskasz pisząc `\iff`).

- Jeżeli więc `∧` jest jak mnożenie (a faktycznie jest), to `True` jest jak liczba `1` *również* w
tym znaczeniu, że jest *elementem neutralnym*, czyli "znikającym w użyciu", ze względu na
*operację binarną* (akurat tutaj na zdaniach, a nie na liczbach), którą oznaczamy w logice za
pomocą symbolu `∧`:

(Może masz ochotę spróbować udowodnić którąś z ostatnich implikacji <nie chodzi o równoważności>?)

*Dla każdego* zdania `p`, `True ∧ p ↔ p ↔ p ∧ True`.

Dla każdej liczby `x`,       `1 × x = x = x × 1`.

Analogiczna sytuacja występuje w przypadku logicznej alternatywy, fałszu, dodawania i zera:
-/

example (p : Prop) : False ∨ p → p := fun h => Or.elim h (fun hF => hF.elim) id
-- i tak dalej (jeżeli ten dowód wydaje Ci się dezorientujący, możesz umieścić kursor nad `Or.elim`
-- i skorzystać z pojawiającego się wtedy okienka pomocy).

/-
Co więcej, w pewnym (bardzo) abstrakcyjnym sensie dodawanie i mnożenie, więc również koniunkcja i
alternatywa, to *jedna i ta sama operacja*, tylko "działająca" *dualnie*. Zresztą `1` i `0` to też
obiekty dualne, czyli (wcale nie tak metaforycznie, jak się może wydawać) wzajemne lustrzane
odbicia, a więc to *ten sam obiekt oglądany z dwóch stron*.

Z faktem, że dodawanie i mnożenie to w zasadzie to samo, można się wstępnie zapoznać przypominając
sobie, że dodawanie staje się mnożeniem, gdy zastosujemy do niego funkcję wykładniczą, a mnożenie
staje się dodawaniem, gdy zastosujemy do niego logarytm, i te dwie funkcje są względem siebie
odwrotne, a więc są również w pewnym sensie jedną i tą samą funkcją, tyle, że "działającą" raz w
jedną, a raz w drugą stronę.

No dobrze, a co z implikacją? Cieszę się, że pytasz. Otóż implikacja jest w pewnym technicznym i
(ekstremalnie) abstrakcyjnym sensie w zasadzie tym samym, co funkcja wykładnicza! I to ma ścisły
związek z curryingiem! A wszystko to jest, przynajmniej moim zdaniem, odrażająco piękne a także
szalenie praktyczne.
-/

----------------------------------------------------------------------------------------------------
-- RÓWNOWAŻNOŚĆ TO KONIUNKCJA TEJ SAMEJ IMPLIKACJI W DWIE STRONY (czyli też pewnego rodzaju
-- "lustrzane odbijanie")

/-
Zdanie o postaci `p ↔ q` (nawet litery są tutaj swoimi odbiciami!) to z definicji to samo, co zdanie
`(p → q) ∧ (q → p)`, ale udowadniamy równoważność korzystając z (dwuargumentowego) konstruktora
`Iff.intro`, a nie z `And.intro`.
-/

example (p : Prop) : p ↔ p := Iff.intro id id
-- Rozumiesz już, jak ten dowód działa? Jeżeli jeszcze nie, spróbuj "rozpakować" definicję stałej
-- `↔` w zdaniu `p ↔ p`.

/-
Zadanie 1: Udowodnij, zastępując `sorry` dowodami zdań `q ∧ p` i `p ∧ q`, twierdzenie, które mówi,
że ─ podobnie jak mnożenie liczb ─ koniunkcja jest *działaniem przemiennym* (na zdaniach). Trzeba tu
tylko zastosować dwa razy `And.intro`, za każdym razem jako argumenty podając dowody prawego i
lewego (w *tej* kolejności) członu koniunkcji, której (hipotetyczny albo "logicznie możliwy" <czy to
znaczy to samo?>) dowód jest w danym miejscu widoczny.
-/

example (p q : Prop) : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro (fun hpq : p ∧ q => sorry) (fun hqp : q ∧ p => sorry)

----------------------------------------------------------------------------------------------------
-- RELACJA MIĘDZY FAŁSZEM I PRAWDĄ (albo TO SAMO - CO ZAWSZE)

-- Skoro z fałszu wynika każde zdanie, a prawda wynika z każdego zdania, to musi być tak, że:

theorem certum_est_quia_impossibile : False → True := fun hF => sorry

/-
Inną nazwą tego twierdzenia mogłoby być credo ut intelligam, albo credo quia absurdum. Warto jednak
pamiętać, że łacińskie "credo" czy nasze "wiara" to niezbyt dokładne tłumaczenie występującego w
Nowym Testamencie starogreckiego słowa "πίστις". To słowo oznaczało nie tylko wiarę, ale również
pewność, dowód, albo *zaufanie*.

Przy okazji dodam, że nazwą *sposobu działania* typu `False` w Leanie jest *absurd*:
-/

#check absurd -- = ex contradictione quodlibet

/-
Żeby istniała funkcja z jednego *zbioru* (tym razem nie typu) do drugiego, *każdy* element
pierwszego zbioru musi mieć dokładnie *jeden* odpowiednik w drugim zbiorze. Istnieje dokładnie
jedna, czyli unikalna funkcja (matematyczna albo funkcja jako program) ze zbioru pustego, czyli
zera, do (każdego) zbioru jednoelementowego, czyli do (funkcjonalnej) jedynki, z dwóch niezależnych
powodów. Po pierwsze, istnieje tylko jeden (pusty) sposób, żeby każdemu elementowi zbioru pustego
przypisać unikalny element *jakiegokolwiek* zbioru. Dlatego sam fakt, że dziedzina jest pusta,
gwarantuje unikalność tej funkcji. Po drugie, sam fakt, że przeciwdziedzina jest zbiorem
jednoelementowym, gwarantuje unikalność funkcji do tego zbioru z każdego zbioru, bo wszystkie
elementy dziedziny, jaka by ona nie była, muszą być posłane do tego samego elementu
przeciwdziedziny. W zasadzie z tego samego powodu dowód twierdzenia `False → True` też można
skonstruować na dwa sposoby (zadanie?).

Ponieważ zbiory o *skończonej* liczbie elementów możemy definiować po prostu *wypisując* wszystkie
elementy (otaczamy je wtedy nawiasami klamrowymi), tą funkcję można zapisać między innymi tak
(ludzie oznaczają elementy zbiorów, jak bydło, niemal dowolnie):

--                                          `{} → {♥}`

O obiektach, które emitują w pewien (bardzo) abstrakcyjny sposób rozumiane *unikalne* strzałki *do
każdego obiektu* (tego samego rodzaju), mówimy w matematyce, że to obiekty początkowe albo początki.
Z kolei o obiektach, które otrzymują w ten sam sposób rozumiane *unikalne* strzałki *od każdego
obiektu* mówimy, że to obiekty końcowe. Między innymi zbiór pusty, zero i typ `False` to obiekty
początkowe, a między innymi (każdy) zbiór jednoelementowy, jedynka i typ `True` to obiekty końcowe.

Z ich definicji wynika, że jeśli w jakimś "matematycznym świecie" istnieją obiekt początkowy (`I`
jak "initial") i końcowy (`T` jak "terminal"), to (z obydwu powodów) istnieje (tak rozumiana)
unikalna strzałka od (każdego takiego) początku do (każdego takiego) końca:

--                                           `I → T`

Strzałka z `False` do `True`, te ze zbioru pustego do każdego singletona, i wiele innych,
niekoniecznie podobnie rozumianych strzałek, to szczególne przypadki tego rodzaju struktury. Jak
widzisz, obiekty początkowy i końcowy to bardzo ogólne pojęcia.

*Jedyna* różnica między definicjami obiektu początkowego i końcowego dotyczy *kierunku* (wszystkich)
strzałek. I właśnie w tym technicznym znaczeniu to są struktury względem siebie dualne, czyli
dokładnie swoje lustrzane odbicia.

Wyobraź sobie teraz wszystkie możliwe *formuły logiczne*, to znaczy formalne zdania, które są albo
zdaniami *atomowymi*, takimi jak `False`, `True` i `p` czy `q`, albo *formułami złożonymi*, to
znaczy koniunkcjami, alternatywami, implikacjami, lub negacjami zdań *niekoniecznie* atomowych.
Wszystkie takie zdania są poprawne *syntaktycznie* (można to rozumieć jako "gramatycznie"), ale nie
wszystkie są oczywiście prawdziwe.

Tak rozumianych zdań jest nieskończenie wiele, bo, dajmy na to, `p ∧ p` jest takim zdaniem, a wobec
tego również `(p ∧ p) ∧ p` jest zdaniem, i tak dalej. Może najlepiej wyobraź sobie `False` na górze,
`True` na samym dole (albo odwrotnie), a między nimi wszystkie inne zdania jako kropki. Wyobraź
sobie też, *że* (czyli nie wyobrażaj sobie tych strzałek, bo jest ich za dużo, tylko wyobraź sobie
pewien *fakt* <?>) od każdego zdania wychodzą strzałki (ale może inaczej rysowane, bo mają oznaczać
coś innego niż implikacje) do każdego takiego zdania, które z tego pierwszego w *jakikolwiek* sposób
logicznie wynika.

To znaczy, że każda taka strzałka ma reprezentować *relację dowiedlności*, czyli sam *fakt*
istnienia dowodu, a nie żaden *konkretny* dowód. To taka różnica jak między *istnieniem* połączenia
i *konkretnymi drogami* między dwoma punktami na mapie. To pierwsze jest pewnym faktem, to drugie
jest elementem mapy, który jest jakby konkretnym "świadkiem" potwierdzającym fakt istnienia
połączenia (podobnie jak każdy dowód jest konkretnym świadkiem albo świadectwem potwierdzającym
prawdziwość pewnego zdania).

W szczególności, każda koniunkcja *emituje* (między innymi) dwie *takie* strzałki do zdań będących
jej członami, i każda alternatywa *dostaje* dwie takie strzałki od zdań będących jej członami. Z
powodu zasady eksplozji dedukcyjnej, zdanie `False` emituje dokładnie jedną taką strzałkę do każdego
zdania, w tym również do siebie, ...
-/

example (jakiekolwiek_zdanie : Prop) : False → jakiekolwiek_zdanie := fun hF => hF.elim

-- ... a definicja zdania `True` z kolei gwarantuje, że każde zdanie, w tym również `True`, emituje
-- dokładnie jedną taką strzałkę do zdania `True`:

example (jakiekolwiek_zdanie : Prop) : jakiekolwiek_zdanie → True :=
  -- zamiast parametru pojawia się tu symbol `_`, bo w tym dowodzie nie korzystamy z parametru
  fun _ => True.intro

/-
W naszej logice jest zatem nie tylko prawdą, że (to, co oznacza zdanie) `False` istnieje co najwyżej
tylko z nazwy albo pozornie, ale w dodatku *wszystkie* drogi prowadzą ostatecznie do Prawdy. Żeby tą
Prawdę "osiągnąć", nie trzeba się jednak ruszać z miejsca, bo Ona zawsze po prostu jest (natychmiast
dostępna). W dodatku jako coś, co jest zarazem w pewnym sensie najważniejsze i w pewnym sensie
najmniej interesujące.

Może już nie tak ważne, ale za to niewątpliwie interesujące są *strzałki ze zdania `True`*, czyli
*wskazane miejsca*, do których można *faktycznie skądś dojść* (w istocie nigdzie się nie ruszając
<skądś, bo w przeciwieństwie do `False`, zdanie `True` jest *o czymś* w tym znaczeniu, że *ma*
dowód>). *Te* strzałki, czyli "prawdziwe wskazania", odpowiadają dokładnie wszystkim *zdaniom
nietrywialnie prawdziwym*, to jest *nieatomowym twierdzeniom*, takim jak `p → p`. Żeby zobaczyć, że
takie strzałki ze zdania `True` odpowiadają dokładnie twierdzeniom logiki, wystarczy zdać sobie
sprawę, że dowód zdania `True` jest jednocześnie ważny i bezużyteczny:
-/

example (p : Prop) : True → (p → p) := fun _ => (fun hp => hp)

/-
Jeżeli jakieś zdanie inne niż `True` (tutaj akurat nasze `p → p`) wynika ze zdania `True`, to dowód
tego zdania można uzyskać nie korzystając z dowodu zdania `True`. A wobec tego strzałki (faktu
spełniania w jakikolwiek sposób relacji) dowiedlności wychodzące ze zdania `True` odpowiadają
dokładnie twierdzeniom logiki. Inaczej mówiąc, formalnie jest tak, że "prawda dowodzi wszystkiego",
co prawdziwe (patrz ostatni przykład), ale "materialnie" nie dowodzi niczego poza sobą (patrz
ostatni przykład).

Podobnie (a dokładniej dualnie) interesujące są (takie) strzałki *do* typu `False`, ponieważ
odpowiadają dokładnie zdaniom *dowiedlnie fałszywym*.

Zinterpretujmy teraz strzałki dowiedlności jako reprezentację relacji *widoczności* albo
*dostrzegalności* czegoś skądś. Bo czemu nie, skoro wnioski dedukcyjne są z jednej strony *zawarte*
w przesłankach, a z drugiej strony, dopóki nie zostaną z nich *wyprowadzone* (jak owce przez
pasterza?), są w nich zawarte niejawnie. Inaczej mówiąc, trzeba (rozważając je jako potencjalny
wniosek) "popatrzeć w ich stronę", z miejsca odpowiadającego przesłankom, żeby je (dedukcyjnie)
"zobaczyć" (jako prawdziwe). Wtedy zmieniają się z wniosków potencjalnych albo implicitnych we
wnioski eksplicitne. Okazuje się więc, że w tej logice prawdą są dokładnie te zdania (`p`), które są
*widoczne z dwóch stron*, to znaczy jednocześnie od strony "obiektywnej", czyli "skądś" ...

-- `True → p`,

... jak i od tej (skrajnie) "subiektywnej", czyli "znikąd":

-- `False → p`

Możemy chyba nazwać tą drugą stronę subiektywną, bo subiektywność jest "meta" w tym znaczeniu, że
nie znajduje "się" *w* spostrzeganej przestrzeni jako część jej zawartości, tylko jest samym
spostrzeganiem albo sposobem spostrzegania. W końcu strzałkami z `False` są dokładnie *jakiekolwiek
zdania*, a subiektywność *jako taką* można rozumieć jako ogół *arbitralnych* zdań.

Można więc również powiedzieć, że prawda (w tej logice) to jakby dokładnie *ugruntowane złudzenia*.
-/

----------------------------------------------------------------------------------------------------
-- CZY TO NA PEWNO "PSYCHOLOGIZOWANIE"?

/-
Funkcje matematyczne można też rozumieć jako formalne odpowiedniki *oznaczania*, bo to po pierwsze
pewne (abstrakcyjne) *pojęcia*, a po drugie to *arbitralne przyporządkowania* ─ każdemu elementowi
jednego zbioru, nazywanego dziedziną funkcji, dokładnie jednego elementu drugiego zbioru, nazywanego
jej przeciwdziedziną. Na przykład, funkcja kwadratowa każdej liczbie przyporządkowuje dokładnie
jedną liczbę (będącą jej kwadratem), i właśnie dlatego nazywamy ten "obiekt" funkcją.

Jeżeli potraktujemy funkcję jako sposób oznaczania, przeciwdziedzina będzie kontekstem, a dziedzina
będzie maksymalnie ubogim językiem, w którym są tylko nazwy własne. Dlatego funkcje nazywamy w
matematyce też "mapami" albo "mapowaniami", czy wreszcie "odwzorowaniami". Każda funkcja może być
więc rozumiana jako jednoczesne nazywanie lub wskazywanie (i może <również> stąd ta strzałka?) jakiś
"rzeczy", "miejsc" albo "własności" w jakimś kontekście (albo w jakiejś "sytuacji").

Jeżeli tak, to *czym* jest, istniejąca unikalnie, funkcja ze zbioru *pustego* do (dowolnego) zbioru
*jednoelementowego*?

--                                         `∅ → {∅}`

Nazywaniem czegoś, będącego *całością* jakiegoś kontekstu, skoro jej przeciwdziedzina to tylko jedno
jakieś coś? Ale przecież, ponieważ dziedzina tej funkcji jest zbiorem pustym, nie ma tu nawet
najuboższego możliwego języka. Czy wobec tego nie można powiedzieć, że taka funkcja jest
*przedjęzykowym oznaczaniem*, czyli *zwracaniem uwagi* na to, co *jest* ("substancja" <essentia
⟦ὠσῐ́ᾱ⟧>), jako na pewną *całość*?

(Nawiasem mówiąc, `∅` to standardowe oznaczenie zbioru pustego, a skoro w tak zwanej "czystej"
teorii mnogości <ZFC> zbiory mogą być *elementami* innych zbiorów, to `{∅}` jest singletonem jak
każdy inny. Zresztą zbiory są w tej teorii *jedynymi* elementami, bo *wszystko* jest tam "zrobione"
ostatecznie ze zbioru pustego!)

I czy zwracanie uwagi nie jest najbardziej fundamentalnym *aktem oceny*? Bo zwracać na coś u*wagę*,
to traktować to coś, choćby na chwilę, jako w jakiś sposób przynajmniej potencjalnie ważne. W
niechęci czy nienawiści jest zawsze pewien elementarny szacunek, bo jeśli coś budzi w nas niechęć,
nienawiść, czy wstręt, to musi być tak, że to coś się dla nas *liczy*. Nie da się, przynajmniej w
pewnym sensie, bardziej negatywnie ocenić czegoś, a zwłaszcza kogoś, niż jako coś nieistotnego.

Albo, jak ujęła to pewna łobuziara: L'attention est la forme la plus rare et la plus pure de la
générosité.

(- Do czego to wszystko zmierza?
 - Sam nie wiem!)

No dobrze (?), ale przecież uwaga to *selekcja* albo *filtrowanie*, a tutaj chodzi o *całość*. W
zasadzie tak, ale redukowanie pojęcia uwagi do pojęcia selekcji jest problematyczne, bo w *samej*
selektywności *jakiegokolwiek* reagowania, na przykład w selektywności rezonansowej odpowiedzi pudła
gitary na drgania powietrza, nie ma *oceny*. A przecież uwaga, tak jak ją rozumiemy w psychologii,
wydaje się zawsze polegać na jakiejś ocenie, bo to jest pojęcie funkcjonalne (w znaczeniu
zdefiniowane w kategoriach wykonywania jakiegoś zadania). Jeżeli rozumiemy uwagę jako (abstrakcyjnie
pojęte) *przykładanie do czegoś wagi*, to może jednak da się, choćby tylko teoretycznie (albo "w
granicy"), zwracać uwagę na *wszystko* (w danym kontekście) *jako na pewną niepodzielną całość*. Tak
jakby ─ swoją Postawą ─ niewerbalnie wypowiadając wobec świata i aktualnego swojego w nim miejsca
niewyrażalne wprost w zwyczajnym języku Wielkie "Tak".

Albo, jak ujął to pewien łobuz: Ainsi je tire de l’absurde trois conséquences, qui sont ma révolte,
ma liberté et ma passion. Par le seul jeu de la conscience je transforme en règle de vie ce qui
était une invitation à la mort — et je refuse le suicide. Inaczej mówiąc, `{} → {♥}`.

Zadanie 2: Gdzie w tym wszystkim jest μῦθος, a gdzie λόγος?

"Substancja" odgrywa w filozofii rolę o tyle szczególną, że ma status terminu technicznego, którego
znaczenie, w przeciwieństwie do słów takich jak "mentalne", "byt", i wielu innych, *nie* wywodzi się
z mowy potocznej. Substancja to to, co jest, a więc dla materialisty to będą obiekty fizyczne albo
materialne, dla dualisty to będą obiekty materialne i stany albo procesy mentalne, i tak dalej. A co
powiesz na interpretację, że "substancją" jest *dla nas* to i tylko to, co (zdaje nam się) stawia(ć)
w jakimkolwiek sensie pewien *opór*? Fizyczne czy materialne obiekty to takie, które opierają się,
przynajmniej do pewnego stopnia, gdy ich dotykamy. Mentalne "obiekty", takie jak myśli, to takie,
które opierają się, przynajmniej do pewnego stopnia, naszym *mentalnym* próbom kontrolowania. Każda,
nawet najbardziej ulotna myśl, ma przecież swoją upartą bezwładność i nie da się jej *natychmiast*
całkowicie "usunąć z głowy".

(- Ile jeszcze będzie tych akapitów?
 - ...)

*Jedyne*, w czym "substancjalność" nam *nigdy* w *żaden* sposób *nie* przeszkadza ─ jest wręcz
przeciwnie, bo zdaje się być konieczna, żeby to coś zachodziło ─ jest *doświadczanie*. Treści
naszego doświadczenia to dokładnie wszystko to, co wydaje nam się nie całkiem kontrolowalne. Zdaniem
niektórych (również filozofów), z jednym wyjątkiem: uniwersalnej postawy ocennej, która akceptuje
samą siebie, bo kiedy (jeśli) pojawia się taka postawa, pojawia się jednocześnie ─ pusta, bo
polegająca na nieróżnicującej akceptacji albo *uniwersalnym przyzwoleniu* ─ pełna kontrola, czyli
nieograniczona wolność.

(- A to też będzie na teście końcowym?
 - Co?)

Czy to nie wrażenie (względnej) "oporności", "stabilności" albo "niezależności" od tego, co wydaje
nam się być działaniem "naszej woli", sprawia, że różne zjawiska postrzegamy jako istniejące
"autonomicznie" i odrębnie, a my, doświadczając ich ─ być może zniekształcająco ─ w zasadzie tylko
je "odzwierciedlamy"? Gdy połączymy to wrażenie i myślowy nawyk z wrażeniem odległości w przestrzeni
między naszym ciałem i innymi ciałami, pojawia się, jak pojęciowe swędzenie, kantowska zagadka
dostępu do "rzeczy samych w sobie". Jako takich rzeczy, które są *poza nami*, ale "jeszcze bardziej
poza" niż te, które znamy, bo jako takie, rzeczy same w sobie istnieją, wydaje się, *na zewnątrz*,
albo wręcz *niezależnie od* lustra percepcji. Tak jakby "rzeczowość", tak samo jak "oporność" czy
"autonomiczność" ─ jakby nie była rozumiana ─ nie była również, jak każda inna, własnością
*relacyjną*.

यः प्रतीत्यसमुत्पादः शून्यतां तां प्रचक्ष्महे । सा प्रज्ञप्तिरुपादाय प्रतिपत् सैव मध्यमा ॥

A ponieważ, kiedy jesteśmy przytomni, działa mechanizm projekcji, to czy nie jest też tak, że
najłatwiej jest nam odkrywać aktualny stan własnego umysłu, przyglądając się temu, jak nam się jawi
"zewnętrzny" świat (szczególnie zaś "inni" ludzie)? Bo introspekcja wychodzi nam tak sobie. Czy
świat taki, jakim nam się w danym momencie jawi ─ czyli świat-w-swoim-istnieniu, bo przecież (za
każdym razem) przeszłego świata już nie ma, a przyszłego jeszcze nie ma ─ nie jest wobec tego w
jakiś sposób naszym najwierniejszym lustrem, pokazującym nam naszą najbardziej subiektywną i
podstawową (i może nawet przedosobową) "postać" albo Postawę?

Ustaliliśmy jak dotąd (?), że Fałsz to jednocześnie Zero, Pustka albo Absolutny Brak inaczej Grzech,
i lustrzane odbicie Istnienia, Jedności i Prawdy.

Nadeszła pora na coś bardziej odklejonego, czyli przyziemnego.
-/

----------------------------------------------------------------------------------------------------
-- NAJWYRAŹNIEJ DOPUSZCZALNE (?) INTERPRETACJE (MIĘDZY INNYMI) LOGICZNEJ RELACJI MIĘDZY FAŁSZEM I
-- PRAWDĄ I TEORIOMNOGOŚCIOWEJ RELACJI MIĘDZY ZBIOREM PUSTYM I KAŻDYM SINGLETONEM
--
--              - Co to jest pion? - pyta Jade.
--              - Przeciwieństwo poziomu, idiotko - wyjaśnia Min.
--
--                                                        (George Sounders, *Morszczyn*)


/-
Logiczna relacja między Fałszem i Prawdą to:

- Sama Uwaga,

- Coś, czego istotą jest Aktywne->Niebycie->Wobec->Istnienia,

- sam Początek Ruchu, z Niebytu do Bytu, albo z Ciemności do Światła,

- Ocena albo Owoc z Drzewa Poznania (Dobrego i Złego),

- Klejnot w Lotosie.

- ॐ मणि पद्मे हूँ

- Ἐγώ εἰμί τὸ Ἄλφα καὶ τὸ Ὦ

- 陰陽

- أنا الحق

Albo, jak ujął to pewien łobuz: Soll Gott gesehen werden... mein Auge und Gottes Auge ist ein Auge
und ein Erkennen und ein Lieben. Inaczej mówiąc, `∅ → {∅}` ~ `{} → {♥}`.

I czy to wszystko nie są w istocie sprawy Psycho-Logiczne?

A z innej beczki, co powiesz na taką dualność, która według niektórych wynika z dualizmu: Dwa
najczęściej występujące rodzaje zaburzeń psychicznych to zaburzenia lękowe i depresyjne. Jedno lub
drugie występuje tak często, że niektórzy nazywają je psychicznym przeziębieniem. Jak zasugerował
rzekomo jeszcze inny łobuz, istotą depresji jest życie  *przeszłością*, a istotą nadmiernego lęku
jest życie *przyszłością*. Nie wiem, czy zaraz  "istotą", ale może przez chwilę "wychodźmy z tego
założenia".

Z tej perspektywy w obydwu przypadkach chodzi o *życie czymś, czego nie ma*. Tak jakby *strzałka
aktywności* była skierowana *od tego, co jest, do tego, czego nie ma*. (Nawiasem mówiąc, w teorii
mnogości i logice zdań takich strzałek nie ma, bo nie spełniałyby jednego z dwóch podstawowych
wymagań dotyczących funkcji). Wspólną istotą obydwu rodzajów zaburzeń jest jednocześnie negatywna
perspektywa albo nastawienie, a mówiąc dokładniej *negatywne złudzenie ocenne*, bo gdyby w tym
ocenianiu nie było daleko idącej przesady, nie mielibyśmy do czynienia z zaburzeniami. W obydwu
przypadkach mamy więc pewną postać *fałszu*. A najgłębsza *różnica* między tymi zaburzeniami wydaje
się, przynajmniej z tej perspektywy, dotyczyć *zwrotu strzałki czasu*. Czyli to też są, przynajmniej
w tym znaczeniu, swoje lustrzane odbicia.

Pobawmy się też może przy okazji zagadką świadomości. Psychologowie od dawna próbują to coś badać,
ale, o ile mi wiadomo, jak dotąd nie udało się ustalić na ten temat nawet *jednego* nietrywialnego
faktu. Kiedy słyszymy takie próby wyjaśnienia, jak to, że chodzi w tym o coś takiego "*jak* bycie
nietoperzem", to chodzi, wydaje się, o pewną *jakość* pewnego *sposobu doświadczania*, a nie o
świadome doświadcz*anie* *jako takie* (w którym chodzi może właściwie o *samo bycie*?).

Świadomość to zdecydowanie nie *punkt* za naszymi oczami, w którym skupiają się promienie światła
wpadające do naszej głowy. Ani to nie jest żadna *przestrzeń* albo ekran, w której pojawiają się
doświadczenia, bo *przestrzenność* to własność albo część *treści* świadomego doświadczenia.
Swiadomość nie jest obiektem materialnym jak każdy inny i nie jest zlokalizowana w przestrzeni; to
przestrzeń, a raczej jej wrażenie, i materialność albo wrażenie "substancjalności" (związane
oczywiście z *doświadczaniem* dotykowym) są czymś "*w*" świadomości. W ogóle wszystko, co *dla nas*
istnieje *z pewnością*, istnieje *tylko aktualnie* i *w* naszej świadomości.

Z tej perpektywy świadomość *jako taka* nie ma właściwości; świadomość tylko *jest* i *tylko* o niej
możemy naprawdę wiedzieć, że jest, zanim jeszcze cokolwiek pomyślimy, co czyni ją jednocześnie
*pustą* i maksymalnie  *obiektywną*. Właściwie nie ma nawet żadnego punktu, *z którego* dopiero coś
widzimy, są tylko *widzenia* w różnych "modalnościach" i punkty, które można *dzięki tym widzeniom*
odnaleźć w  dostępnych *w ramach* tych widzeń (w takim lub innym sensie) przestrzennych treściach.

To już może I=Will See-My-Self-Out 😘
-/

----------------------------------------------------------------------------------------------------
-- BTW, Q.E.D. (FR, chyba, że znajdziesz kontrargument)

/-
Zadanie 3: Tym razem zamiast *udowadniać*, że jakieś *zdanie* jest *prawdziwe* lub *fałszywe*,
spróbuj *zademonstrować*, że któraś z przytoczonych *interpretacji* jest *nieadekwatna* lub
*bezużyteczna*.

Dlaczego i po co? Może na przykład dlatego, że w psychologii ─ nie tylko w kontekście terapii ─
interpretacje odgrywają niezwykle doniosłą rolę? I po to, żeby zarówno same te interpretacje, jak i
to, czego dotyczą, trochę lepiej w ten sposób zrozumieć? Ale uwaga: niespójność lub paradoks
niekoniecznie prowadzi do bezużyteczności! (patrz hasło "logika parakonsystentna", albo przypomnij
sobie, co zmarła niedawno wspaniała Marsha Linehan mówiła o roli *dialektyki* w procesie terapii).

Można powiedzieć, że czasem naginam tu język, ale czy faktycznie? Jeżeli jakąś perspektywę da się
*konsekwentnie stosować*, to ta perspektywa po prostu jest i raczej nic się w niej nie zgina.
*Zmiana* perspektywy, tak ważna między innymi w procesie terapii, albo gdy próbujemy coś
teoretycznie wyjaśniać czy głębiej zrozumieć, to co innego; wtedy Coś się w jakimś sensie *rusza*,
ale właściwie co? Czy może raczej Kto? Kim jest ten Ów, który istnieje jeszcze zanim przyjmie jakąś
perspektywę? Czy ten jakiś Ktoś, to nie przypadkiem, wydaje się wręcz, że z trudnej do uchwycenia
definicji ─ we Własnej Osobie ─ sam Widok Znikąd?

(Biega, krzyczy pan Hilary: "Gdzie są moje okulary?")

Na koniec wypada wspomnieć, że (może niespodziewanymi) niejawnymi bohaterami tego odcinka byli
między innymi ─ w mojej ocenie wybitni Psycho-Logowie ─ Sutton i Barto, Spinoza, Nagardżuna, Simone
Weil, Albert Camus, Al-Halladż, Mistrz Eckhart, św. Augustyn, Ten, który Obudził się na jawie, Ten,
który został Namaszczony, Arthur Schopenhauer i Thomas Nagel 🫥
-/













































































































































































































-- PS Jeżeli interesuje Cię celowość wprowadzania takiej rozpiętości rejestrów w tego rodzaju
-- kontekście, to może zainteresuje Cię też wprowadzenie do "Pagan Mysteries in the Renaissance"
-- Edgara Winda.
