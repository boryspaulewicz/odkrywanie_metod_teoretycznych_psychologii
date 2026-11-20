----------------------------------------------------------------------------------------------------
-- RACHUNEK PREDYKATÓW WYŻSZEGO RZĘDU

-- Jak być może pamiętasz z lektury wprowadzenia do książki Alyssy Nye, oczywista (a więc "dana" nam
-- jeszcze zanim zaczynamy się uczyć logiki *formalnej*) "formalna" poprawność rozumowań takich jak
-- ...
--
-- Jeżeli każdy człowiek jest śmiertelny i Donald Trump jest człowiekiem, to Donald Trump jest
-- śmiertelny.
--
-- ... *nie może* być uchwycona w rachunku *zdań*, ponieważ zakodowanie tego rozumowania w rachunku
-- zdań musi wyglądać tak ...
--
-- `p ∧ q → r`
--
-- ... gdzie `p` to formalny odpowiednik zdania "Każdy człowiek jest śmiertelny", i tak dalej.
-- Ewentualnie tak ...
--
-- `p → q → r`
--
-- ... co, jak już wiesz, w zasadzie na jedno wychodzi, bo istnienie curryingu sprawia, że te dwa
-- rodzaje typów są *uniwersalnie mechanicznie zastępowalne*: *Każdą* funkcję pobierającą dwa
-- argumenty można zastąpić, *w taki sam działający ogólnie* (czyli taki jakby "formulaiczny")
-- sposób, funkcją jednoargumentową zwracającą funkcję jednoargumentową i odwrotnie, *nie zmieniając
-- "funkcjonalności" tych funkcji*.
--
-- W każdym razie, żadne z tych dwóch zdań nie jest twierdzeniem logiki, to znaczy, żadne z nich nie
-- jest uniwersalnie albo formalnie prawdziwe (albo udowadnialne). A nasze rozumowanie, dotyczące
-- *między innymi* Donalda Trumpa, jest ewidentnie prawdziwe formalnie, to znaczy w taki sposób,
-- który nie zależy od konkretnych cech ("śmiertelność" i "człowieczeństwo") ani egzemplarzy czy
-- tokenów (Donald Trump).

-- W *języku* rachunku zdań *atomami* są *zdania*, które z perspektywy tego języka nie mają już
-- wewnętrznej struktury, czyli to są "jakieś" zdania (albo zdania parametry!).
--
-- W *języku* rachunku predykatów *atomami* są *predykaty*, odpowiadające takim wyrażeniom języka
-- naturalnego jak "jest śmiertelny", i *termy*, których te predykaty dotyczą, odpowiadające nazwom
-- własnym takim jak "Stefan".
--
-- *Zdania* w języku predykatów to nic innego jak *aplikacje* funkcji zwracających *zdania*!

variable (P : Nat → Prop) -- Niech `P` będzie jakąś funkcją z `Nat` do `Prop`, ...
#check P 2 -- P 2 : Prop  -- ... wtedy `P 2` ma typ `Prop`, czyli jest zdaniem.

-- `P` to tutaj (jakiś) predykat (można też myśleć "cecha") dotyczący liczb naturalnych, wobec czego
-- `P 2` to *jednocześnie* aplikacja funkcji `P` do termu `2` i *zdanie złożone* z *podmiotu* `2` i
-- *orzeczenia* `P`. Czy zaczynasz już dostrzegać, że opanowanie technicznych podstaw języka teorii
-- typów pozwala zacząć szybciej rozumieć niektóre pozornie niesprowadzalne do tego samego teorie
-- matematyczne (tutaj akurat dwa rodzaje logik)?

-- Uwaga: Podobnie jak to miało miejsce w rachunku zdań, samo `P 2` to tutaj *zdanie*, a nie
-- *stwierdzenie, że zdanie `P 2` jest prawdziwe*. Takie (s)twierdzenie musi mieć postać *dowodu*
-- (nawet jeśli tylko hipotetycznego) tego zdania.

----------------------------------------------------------------------------------------------------
-- DUŻY KWANTYFIKATOR MASZ JUŻ OPAN(I)OWANY

-- Przypominam naszą identycznościową tautologię (tym razem w wersji maksymalnie wykrochmalonej):

theorem idProp (p : Prop) : p → p := fun (hp : p) => hp

-- `p` jest tutaj *zmienną*, inaczej *parametrem*, bo tu chodzi o *jakieś*, bliżej nieokreślone
-- zdanie `p`. Czasem wyrażaliśmy tą "zmiennościowość" za pomocą deklaracji `variable`, czasem
-- traktując `p` jako lokalny parametr (na przykład, gdy `(p : Prop)` pojawiało się zaraz po
-- `example`), a czasem używając parametryzacji implicitnej (gdy były nawiasy klamrowe), ale za
-- każdym razem to było *jakieś* zdanie, czyli to był parametr, czyli to była zmienna.

-- To znaczy, że wszystkie nasze twierdzenia zostały odowodnione *dla dowolnego* zdania `p`, inaczej
-- mówiąc *dla każdego* `p`. Symol `∀` (który uzyskasz pisząc `\forall`) to tylko *alternatywna
-- notacja* dla czegoś, czego używaliśmy przez cały czas. W szczególności, to ...

theorem idProp' : ∀ p : Prop, p → p := fun p : Prop => fun hp : p => hp

-- ... jest *to samo* twierdzenie, tylko *inaczej zapisane*; różnica jest całkiem powierzchowna.

----------------------------------------------------------------------------------------------------
-- AKSJOMATY TO NIE ZAŁOŻENIA TYLKO DECYZJE ALBO WYBORY JĘZYKOWE

-- *Aksjomaty* to *decyzje* dotyczące tego, jak będziemy *używać* pewnych *konkretnych symboli*.
-- Aksjomaty są więc *definicjami*. W teorii typów to się sprowadza do *decyzji o typie*.

-- `Człowiek` to typ jak każdy inny, bo tak:
axiom Człowiek : Type
-- `Śmiertelny` to predykat dotyczący termów typu `Człowiek`, bo tak:
axiom Śmiertelny : Człowiek → Prop
-- A to jest dowód śmiertelności każdego człowieka, bo tak:
axiom ludzie_umierają : ∀ c : Człowiek, Śmiertelny c
axiom Donald_Trump : Człowiek

#check ludzie_umierają -- ludzie_umierają (c : Człowiek) : Śmiertelny c
#check @ludzie_umierają -- ludzie_umierają : ∀ c : Człowiek, Śmiertelny c
example : (c : Człowiek) → Śmiertelny c := ludzie_umierają

-- Czy widzisz, że te trzy sposoby zapisu znaczą to samo?

-- `Śmiertelny Donald_Trump` to teraz zarazem zdanie i *twierdzenie* naszej teorii, które możemy
-- udowodnić stosując *aksjomat parametryczny* `ludzie_umierają` do termu `Donald_Trump`:

example : Śmiertelny Donald_Trump := ludzie_umierają Donald_Trump

-- Aksjomaty parametryczne nazywamy po polsku "schematami aksjomatu". "Schematami", bo to są formuły
-- generujące tyle aksjomatów, ile możemy im dostarczyć termów (matematycy zwykle mówią "obiektów")
-- wymaganego typu. Nasz schemat aksjomatu zwraca dowód pewnego zdania dla każdego termu typu
-- `Człowiek`. A zatem `ludzie_umieraja` to dokładnie *funkcja zwracająca aksjomatyczne dowody*.
-- Jeszcze raz: to nie jest żadne *założenie*; za pomocą tej aksjomatycznej funkcji wyrażamy
-- *definicyjną* relację między pojęciami człowieczeństwa i śmiertelności.

-- Zadanie 1: Znajdź brakujący term przyglądając się temu, jak kolejne kroki konstrukcji
-- interaktywnej zmieniają stan taktyczny (i w ten sposób domyślając się, jak działa taktyka `rw`).
example : ∀ a b c : Nat, (a = b) → ((b = c) → (a = c)) := by -- te wszystkie nawiasy są zbędne
  -- Ponieważ mamy tu do czynienia z implikacją do implikacji, to może jeszcze raz wyjaśnię:
  -- Nieważne, jak bardzo zagnieżdżona byłaby implikacja (a ogólnie *dowolny* typ strzałkowy),
  -- dowodzenie takiej zagnieżdżonej implikacji (a ogólnie konstruowanie termu dowolnie
  -- zagnieżdżonego typu strzałkowego) polega zawsze na "założeniu" (czyli na "posiadaniu", a może
  -- raczej "otwarciu się na"?) zmiennych-parametrów o postaci hipotetycznych dowodów, a ogólnie
  -- hipotetycznych termów typu *każdego poprzednika*, i na konstrukcji dowodu (a ogólnie termu
  -- typu) jej ostatecznego następnika (tutaj `a = c`).
  intro a b c hab hbc
  -- Również `a`, `b` i `c` są tu (niejawnymi) "poprzednikami" typu strzałkowego (!), bo wyrażenie
  -- `∀ a b c : Nat` to tylko alternatywny sposób zapisania `(a b c : Nat)`, a to z kolei inny
  -- sposób zapisania `(a : Nat) (b : Nat) (c: Nat)`, a to jest tylko inny sposób zapisania
  -- wyrażenia `(a : Nat) → (b : Nat) → (c : Nat)`.
  rw [hab]
  -- Nazwa taktyki `rw`, która przekształca cel, to skrót od "rewrite". Jeżeli nie powiemy jej nic
  -- więcej, `rw [coś]`, gdzie `coś : X = Y`, zastąpi *pierwsze* wystąpienie `X` w *celu* przez `Y`.
  -- Żeby zastąpić w celu *prawą* stronę równania przez *lewą* piszemy `rw [←coś]` (`←` uzyskasz
  -- pisząc `\left`).
  rw [sorry]

-- Masz już opanowany duży kwantyfikator na poziomie logiki *wyższego* rzędu, ponieważ w teorii
-- typów możemy kwantyfikować po *każdym* możliwym typie. Na przykład:

-- Zadanie 2
example : ∀ typ : Type, ∀ a b c : typ, a = b → b = c → a = c := by -- tym razem bez zbędnych nawiasów
  intro typ x y z hxy hyz -- nazwy parametrów nie są widoczne z zewnątrz funkcji → nie mają znaczenia
  sorry

-- Jak zatem *udowadniamy* zdania o po staci `∀ x : X, Cośtam x`? Tworząc funkcje przekształcające
-- dowolne termy `x` o typie `X` w termy typu / dowody zdania `Cośtam x`. A jak korzystamy z takich
-- (czyli "uniwersalnie kwantyfikowanych") twierdzeń w dowodach? Aplikując ich dowody, czyli pewne
-- funkcje, do termów odpowiedniego typu. Duży kwantyfikator to dla nas po prostu *parametryczność*
-- jak każda inna:

-- Dowód zdania `∀ a b c : Nat, a = b → b = c → a = c` to funkcja przekształcająca *każde* trzy
-- termy typu `Nat` w dowód zdania zapisanego po przecinku.

-- Termem typu `Nat → Nat` jest każda funkcja przekształcająca *każdy* term typu `Nat` w termy typu
-- `Nat`, a więc możemy również pisać tak:

def dodaje1 : ∀ n : Nat, Nat := fun n : Nat => n + 1 -- wiem, że początkowo to wygląda dziwnie
#check dodaje1  -- `dodaje1 (n : Nat) : Nat`
#check @dodaje1 -- `dodaje1 : Nat → Nat`
#eval dodaje1 2 -- `3`

-- Gratulacje: Wiesz w tym momencie wszystko, co potrzebujesz wiedzieć o dużym kwantyfikatorze w
-- logice predykatów wyższego rzędu i *jednocześnie* znasz się już trochę na programowaniu
-- funkcyjnym. I *jednocześnie* wiesz teraz pewne ważne rzeczy na temat podstaw całej matematyki, a
-- więc na temat *wszystkiego*, co jest (w tym sensie) *formalizowalne*. W dodatku możesz to
-- wszystko ćwiczyć *samodzielnie*, korzystając z informacji zwrotnych dostarczanych przez Leana.

----------------------------------------------------------------------------------------------------
-- KWESTIA ISTNIENIA

-- Symbol `∃` uzyskasz pisząc `\exists`. Duży kwantyfikator (nazywany też uniwersalnym) jest jak
-- *koniunkcja*: dla każdego `x`, ..., a więc dla tego `x` *i* dla tamtego `x` *i* dla tamtego, i
-- tak dalej. Kwantyfikator egzystencjalny, nazywany też małym albo szczegółowym, jest jak
-- *alternatywa*: istnieje takie `x`, że ..., a więc dla tego `x` albo dla tego `x` albo dla tego, i
-- tak dalej.

-- Duży kwantyfikator jest jak *koniunkcja indeksowana termami*. Na przykład, ...
--
-- `∀ n : Nat, P n`, gdzie `P : Nat → Prop`,
--
-- ... znaczy w zasadzie to samo, co ...
--
-- `(P 1) ∧ (P 2) ∧ ...`,
--
-- ... chociaż nie da się korzystać z `∀ n : Nat, P n` jakby to była *formalna* koniunkcja.
--
-- Analogicznie, mały kwantyfikator jest jak *alternatywa indeksowana termami*:
--
-- `∃ n, P n` ~ `(P 1) ∨ (P 2) ∨ ...`
--
-- A więc to "tylko" uogólnienia koniunkcji i alternatywy.

-- Już wiesz, że udowadniamy zdania kwantyfikowane uniwersalnie tworząc odpowiednie funkcje, a
-- używamy (dowodów) takich zdań w dowodach po prostu aplikując te funkcje.
--
-- Zdania kwantyfikowane egzystencjalnie udowadniamy *dostarczając parę* złożoną z termu
-- odpowiedniego typu i dowodu, że ten term spełnia kwantyfikowane zdanie:

example : ∃ n : Nat, n = 0 := ⟨0, Eq.refl 0⟩

-- Symbol `⟨` uzyskasz pisząc `\<` (analogicznie uzyskasz `⟩`). Term o postaci `⟨x, y⟩` to para
-- uporządkowana złożona z termów `x` i `y`. `Eq.refl` to nazwa dowodu zwrotności relacji równości,
-- czyli dowodu zdania, że dla każdego `x`, `x = x`, niezależnie od tego, jakiego typu jest `x` (ta
-- funkcja używa więc parametrów implicitnych).

-- *Typ* par uporządkowanych zapisujemy w ten sposób (`×` uzyskasz pisząc `\times`):

#check Nat × String -- Nat × String : Type
example : Nat × String := ⟨1, "dwa"⟩

-- Żeby wykorzystać zdanie egzystencjalne `∃ x : X, P x` do udowodnienia np. `∀ y : Y, R y`,
-- korzystamy z dowodu zdania *uniwersalnego* `∀ x : X, P x → (∀ y : Y, R y)`. A to dlatego, że
-- zdanie egzystencjalne *nie* mówi nam *jaki* term spełnia dane zdanie, mówi nam tylko, że `jakiś`.
-- Analogiczna sytuacja występuje w przypadku alternatywy: żeby wykorzystać dowód alternatywy w
-- dowodzie, musimy użyć dowodów wynikania czegoś z *każdego* członu alternatywy.

-- Pokażę Ci teraz przy okazji wygodny sposób używania dowodów zdań egzystencjalnych.

-- Tak się nazywa twierdzenie, że `0` jest najmniejszą liczbą naturalną (`≤` uzyskasz pisząc
-- `\leq`):

example (P : Nat → Prop) : (∃ n : Nat, P n) → ¬(∀ m : Nat, ¬(P m)) :=
  fun ⟨n, hpn⟩ => by -- możemy wejść w tryb interaktywny w dowolnym momencie definiowania termu
  intro h
  unfold Not at h -- żeby było lepiej widać, o co chodzi
  apply h n -- `apply` przyjmuje również złożone termy o typie strzałkowym
  exact sorry

-- Ponieważ dowód zdania egzystencjalnego można skonstruować tylko w *jeden* sposób, to Lean może
-- się sam domyślić, że każdy term o typie zdania egzystencjalnego to para uporządkowana złożona z
-- termu i dowodu pewnego zdania (zwykle dotyczącego tego termu). Dlatego możemy w taki wygodny
-- sposób jak wyżej *przechwycić* składowe tej pary *w parametrze*, pisząc na przykład, jak wyżej,
-- `fun ⟨n, hpn⟩ => ...`.

-- Ten sam sposób działa dla koniunkcji, dokładnie dlatego, że jest tylko *jeden* sposób
-- konstruowania dowodu koniunkcji:

example (p q : Prop) : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩

-- Poza tym, jak widzisz, zamiast korzystać z `And.intro`, dowody koniunkcji możemy również
-- zapisywać wprost jako pary (dowodów jej członów) i to działa tak samo dla *równoważności*, która
-- jest z definicji koniunkcją dwóch implikacji:

example (p : Prop) : p ↔ p := ⟨id, sorry⟩

-- Szybko poszło, prawda? A to dlatego, dowód `p → p` to pewna identyczność (na zdaniach), a `id` to
-- taka identyczność uniwersalna, z typem przetwarzanego termu jako niejawnym parametrem.

-- Ten trik *nie* działa w przypadku alternatyw i zdań uniwersalnych, ponieważ, w ogólnym przypadku,
-- tego rodzaju zdania można udowodnić na *więcej niż jeden* sposób, wobec czego Lean nie może
-- zakładać "formulaicznej" struktury tych dowodów.

-- GRATULACJE: Wiesz już wszystko, co potrzebujesz wiedzieć na temat rachunku predykatów wyższego
-- rzędu (w wersji konstruktywnej). Co prawda nie "masz" go jeszcze "w palcach", ale od tego są
-- *ćwiczenia* i ich *powtarzanie*, najlepiej na *różne* sposoby ─ na przykład, raz interaktywnie, a
-- raz pisząc kod wprost ─ o czym w następnym odcinku.
