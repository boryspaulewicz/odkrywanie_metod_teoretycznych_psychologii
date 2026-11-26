-- To jest skrócona wersja pierwszego skryptu, która ma ułatwiać powtarzanie materiału.

-- *Teoria typów* to teoria *syntaktyczna*, to znaczy, określająca reguły tworzenia wyrażeń, a nie
-- ich sens; sens(y) nadajemy jak chcemy.

-- Poprawne wyrażenia w teorii typów to tak zwane *termy*. Każdy term ma unikalny *typ* (`1 : Nat`),
-- a każdy typ jest termem jakiegoś typu (`Nat : Type`). Typy zawierające strzałkę (`Nat → Nat`) to
-- typy *funkcji*. Wszystko, co "dzieje się" w matematyce, dzieje się dzięki funkcjom, a raczej
-- dzięki temu, jak *my ich używamy*.

-- Funkcja `Nat.succ` zwraca następną liczbę naturalną:
#check @Nat.succ -- `Nat.succ : Nat → Nat`
#eval Nat.succ 1 -- `2`

-- To *definicja* (`def ... := ...`) stałej o nazwie `ss` jako funkcji, która *ma parametr* czyli
-- *wejście* typu `Nat` (`(n : Nat)`), co znaczy, że *akceptuje i przetwarza argumenty* tego typu, i
-- *zwraca rezultat* typu `Nat` (`: Nat`), czyli ma takie *wyjście*. Ta funkcja w swoim *ciele*
-- (`Nat.succ (Nat.succ n)`) dwukrotnie *stosuje* funkcję `Nat.succ` do *argumentu*, który *na
-- skutek ewaluacji zastosowania* tej funkcji stał się *wartością jej parametru*:
def ss (n : Nat) : Nat := Nat.succ (Nat.succ n)

-- Notacja `(n : Nat) : Nat` to tylko jedna z konwencji. Tą samą funkcję możemy zdefiniować tak
-- (nadając jej inną nazwę <to przykład *przestawialności głównego dwukropka* w definicjach
-- *funkcji*: zamiast `(n : Nat) : Nat` piszemy `: Nat → Nat`>):
def ss' : Nat → Nat := (fun (n : Nat) => Nat.succ (Nat.succ n))
-- Czytamy to: Definiuję `ss'` jako stałą typu `Nat → Nat`, czyli funkcję z `Nat`-ów do `Nat`-ów.
-- Wartością tej stałej jest funkcja (anonimowa), stosująca do *dowolnego* (dlatego to jest
-- *zmienna*) termu `n` typu `Nat` kod `Nat.succ (Nat.succ n)`.

#eval ss 1 -- `3`
#eval ss' 1 -- `3`

-- Gdy *zestawiamy* ze sobą funkcję `ss` i jakiś akceptowalny przez nią *argument*, czyli gdy tylko
-- *zapiszemy takie dwa termy obok siebie*, uzyskujemy *od razu, jeszcze przed obliczeniem wyniku*,
-- term (złożony) typu `Nat`, bo *samo* takie zestawienie (nazywane *aplikacją*) jest już opisem
-- unikalnej liczby naturalnej:
#check ss 1 -- `ss 1 : Nat`

-- Inaczej mówiąc: `ss 1 : Nat`, bo `ss : Nat → Nat` i `1 : Nat`.

-- Gdy kursor znajduje się na linii `#eval ...` powyżej, Lean *rozpakowuje definicję* stałej `ss`.
-- Treścią tej definicji jest funkcja *anonimowa*, ...
#check (fun (n : Nat) => Nat.succ (Nat.succ n)) -- `... : Nat → Nat`

-- ... a ponieważ w `ss 1` mamy argument `1`, to uzyskujemy (po rozpakowaniu definicji `ss`) taką
-- oto aplikację o typie `Nat`:
#check (fun (n : Nat) => Nat.succ (Nat.succ n)) 1 -- `... : Nat`

-- Ewaluacja (która w tym wypadku jest nazywana też *redukcją*) tej aplikacji polega po prostu na
-- *podstawianiu* i (ewentualnym) dalszym *redukowaniu aplikacji*, to znaczy na tym, że Lean *odrywa
-- ciało funkcji*, czyli część definicji funkcji występującą po symbolu `=>`, ...

-- `Nat.succ (Nat.succ n)`

-- ... i *podstawia argument we wszystkie miejsca wystąpienia (zmiennego) parametru*:
#check Nat.succ (Nat.succ 1) -- `... : Nat`

-- W ten sam sposób ewaluuje (rozpakowując definicję `Nat.succ`, a potem redukując przez
-- podstawianie i odrzucanie części `fun ... =>`) aplikację `Nat.succ 1`, a gdy już obliczy rezultat
-- (`2`), tak samo ewaluuje `Nat.succ 2`. Ponieważ rezultat tej ostatniej aplikacji (`3`) *nie* jest
-- już aplikacją, ewaluacja się na tym kończy.

-- Dlatego każdą definicję funkcji można rozumieć jak pudełko, które ma jedno lub więcej wejść
-- określonego typu (tutaj `(n : Nat)`), jedno wyjście określonego typu (tutaj `Nat`), a w środku
-- którego to pudełka są "przewody" od wejść do jakiś wewnętrznych pudełek (czyli innych funkcji
-- aplikowanych do parametrów w ciele tej funkcji, tutaj `Nat.succ`), których wyjścia, być może
-- przechodząc przez jakieś wewnętrzne pudełka (tutaj wyjście "pierwszego" pudełka `Nat.succ` jest
-- podłączone do jeszcze jednego pudełka `Nat.succ`), ostatecznie zmierzają do wyjścia definiowanej
-- funkcji.

-- Na przykład, definicję `ss` można (w wymyślonej przeze mnie notacji) "zobrazować" tak,
-- interpretując `:` jako zewnętrzny "interfejs", a `-->` jako "przewody kierunkowe":

-- `Nat : --> Nat.succ --> Nat.succ --> : Nat`

-- Czytamy to: Pobieram `Nat-y`, które przepuszczam przez maszynkę o nazwie `Nat.succ`, wynik
-- przepuszczam znowu przez `Nat.succ`, i ostatecznie zwracam rezultat typu `Nat`. Zastosowana tu
-- "graficzna" notacja "przewodowa" sprawia, że *nazwy parametrów stają się zbędne*, ponieważ de
-- facto *są* zbędne:

-- *Parametry to, istniejące dla naszej wygody, oznaczenia połączeń między funkcjami, z aplikacji
-- których składa się dana funkcja*.

-- Gdyby w Leanie można było robić tylko takie rzeczy, byłby to język programowania funkcyjnego jak
-- każdy inny. Ale można robić w nim również takie rzeczy (co sprawia, że w teorii typów można
-- sformalizować praktycznie całą matematykę):

def uogólniona_identyczność (typ : Type) (parametr : typ) : typ := parametr

-- Tą funkcję dwuargumentową można stosować do argumentów różnego typu, trzeba jej tylko powiedzieć,
-- jakiego:
#eval uogólniona_identyczność Nat 1 -- 1
#eval uogólniona_identyczność String "2" -- "2"

-- Typ funkcji `uogólniona_identyczność` to przykład *typu zależnego* (przez co ta funkcja jest
-- <parametrycznie> *polimorficzna*), bo *to, jakiego typu jest ta funkcja, zależy od argumentu*,
-- który podamy jej na wejściu. Konkretnie, *typ* drugiego *parametru* jest tu *wartością*
-- pierwszego *parametru*:

-- `uogólniona_identyczność Nat 1`
--> (rozpakowanie definicji):

-- `(fun (typ : Type) => (fun (parametr : typ) => parametr)) Nat 1`
--> (oderwanie ciała i podstawianie):

-- `(fun (parametr : Nat) => parametr) 1`
--> (oderwanie ciała i podstawianie):

-- `1`

-- Dzięki temu, że w teorii typów mamy *typy zależne*, rezultaty *tych* (częściowych) aplikacji
-- mają *różne* typy:
#check uogólniona_identyczność Nat    -- `... : Nat → Nat`
#check uogólniona_identyczność String -- `... : String → String`

-- To właśnie dzięki typom zależnym teoria typów to język programowania, w którym zdania (takie jak
-- `¬p`, `p → q`, `p ∧ q`, czy `p ∨ q`, gdzie `p q : Prop`), to typy jak każde inne, a *dowody* to
-- dokładnie *termy typów zdaniowych* (np. `(fun (hp : p) => hp) : p → p`), czyli *programy
-- komputerowe* lub *struktury danych*, które *mają jakieś zdanie jako swój typ*. To dzięki typom
-- zależnym można uprawiać całą matematykę jakby to było zwykłe programowanie.

-- (Nawiasem mówiąc, to są dowody tożsamości funkcji `ss` i `ss'`. Dowiesz się, co się tu dzieje, w
-- następnych skryptach.)
example : ∀ (n : Nat), (ss n) = (ss' n) := by intro n; rfl
example : ss = ss' := by rfl

-- Byłoby wspaniale, gdyby udało Ci się czasami potwórzyć, pisząc to, jak je rozumiesz, na kartce
-- całymi zdaniami, treść następujących pojęć:
--
-- Term, typ, sprawdzanie typu inaczej typowanie, funkcja, parametr, przestawialność głównego
-- dwukropka w definicjach funkcji, argument, typy zależne, ewaluacja
