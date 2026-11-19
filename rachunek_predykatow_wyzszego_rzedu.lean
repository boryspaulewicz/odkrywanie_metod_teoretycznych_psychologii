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

-- Przypominam naszą identycznościową tautologię:

theorem idProp (p : Prop) : p → p := fun hp => hp

-- `p` jest tutaj *zmienną*, inaczej *parametrem*, czyli tu chodzi o *jakieś*, bliżej nieokreślone
-- zdanie `p`. Czasem wyrażaliśmy ten fakt za pomocą deklaracji `variable`, czasem traktując `p` jak
-- lokalny parametr, a czasem używając parametryzacji implicitnej, ale za każdym razem to było
-- *jakieś* zdanie.

-- To znaczy, że wszystkie nasze twierdzenia zostały odowodnione *dla dowolnego* zdania `p`, inaczej
-- mówiąc *dla każdego* `p`. Symol `∀` (który uzyskasz pisząc `∀`) to tylko *alternatywna notacja*
-- dla czegoś, czego używaliśmy przez cały czas. W szczególności, to ...

theorem idProp' : ∀ p : Prop, p → p := fun p : Prop => fun hp : p => hp

-- jest to samo twierdzenie, tylko inaczej zapisane.

-- *Aksjomaty* to *decyzje* dotyczące tego, jak będziemy *używać* pewnych *konkretnych symboli*. W
-- teorii typów to się zawsze sprowadza do *decyzji o typie*.

axiom Człowiek : Type -- `Człowiek` będzie dla nas typem, jak każdy inny
axiom Śmiertelny : Człowiek → Prop -- `Śmiertelny` będzie predykatem dotyczącym termów typu `Człowiek`
axiom wszystko_mija : ∀ c : Człowiek, Śmiertelny c -- a to będzie dowód śmiertelności każdego człowieka
axiom Donald_Trump : Człowiek

#check wszystko_mija -- wszystko_mija (c : Człowiek) : Śmiertelny c
example : (c : Człowiek) → Śmiertelny c := wszystko_mija
#check @wszystko_mija -- wszystko_mija : ∀ c : Człowiek, Śmiertelny c

-- Czy widzisz, że te trzy sposoby zapisu znaczą to samo?

-- `Śmiertelny Donald_Trump` to teraz *twierdzenie* naszej teorii, które możemy udowodnić stosując
-- *aksjomat parametryczny* (czyli tak zwany "schemat aksjomatu", czyli pewną istniejącą
-- aksjomatycznie *funkcję*) `wszystko_mija` do termu `Donald_Trump`:

example : Śmiertelny Donald_Trump := wszystko_mija Donald_Trump

-- Zadanie 1: Znajdź brakujący term przyglądając się temu, jak kolejne kroki konstrukcji
-- interaktywnej zmieniają stan taktyczny.
example : ∀ a b c : Nat, (a = b) → ((b = c) → (a = c)) := by -- te wszystkie nawiasy są zbędne
  -- Nieważne, jak bardzo zagnieżdżona byłaby implikacja (a ogólnie *dowolny* typ strzałkowy),
  -- dowodzenie takiej zagnieżdżonej implikacji (a ogólnie konstruowanie termu dowolnie
  -- zagnieżdżonego typu strzałkowego) polega zawsze na "założeniu" (czyli na "posiadaniu"
  -- zmiennych-parametrów o postaci hipotetycznych dowodów, a ogólnie hipotetycznych termów typu)
  -- *każdego poprzednika* i na konstrukcji dowodu (a ogólnie termu typu) jej ostatecznego
  -- następnika (tutaj `a = c`).
  intro a b c hab hbc
  rw [hab] -- nazwa taktyki `rw`, która przekształca cel, to skrót to "rewrite" (za pomocą)
  rw [sorry]

-- Masz już opanowany duży kwantyfikator na poziomie logiki wyższego rzędu, ponieważ w teorii typów
-- możemy kwantyfikować po *każdym* typie, niezależnie od tego, jak bardzo byłby złożony. Na
-- przykład:

-- Zadanie 2
example : ∀ typ : Type, ∀ a b c : typ, a = b → b = c → a = c := by -- tym razem bez zbędnych nawiasów
  intro typ a b c hab hbc
  sorry

-- Jak zatem *udowadniamy* zdania o poI możesz to wszystko powtarzać samodzielnie
-- staci `∀ x : X, Cośtam x`? Tworząc funkcje przekształcające
-- dowolne termy `x` o typie `X` w termy typu albo dowody zdania `Cośtam x`. A jak korzystamy z
-- takich zdań w dowodach? Aplikując ich dowody czyli pewne funkcje do termów odpowiedniego typu.
-- Duży kwantyfikator to dla nas po prostu *parametryczność* jak każda inna:

-- Dowód zdania `∀ a b c : Nat, a = b → b = c → a = c` to funkcja przekształcająca trzy termy typu
-- `Nat` w dowód zdania zapisanego po przecinku.

-- Termem typu `Nat → Nat` jest każda funkcja przekształcająca termy typu `Nat` w termy typu `Nat`,
-- a więc możemy również pisać tak:

def dodaje1 : ∀ n : Nat, Nat := fun n : Nat => n + 1
#check dodaje1  -- `dodaje1 (n : Nat) : Nat`
#check @dodaje1 -- `dodaje1 : Nat → Nat`
#eval dodaje1 2 -- `3`

-- Gratulacje: Wiesz w tym momencie wszystko, co potrzebujesz wiedzieć o dużym kwantyfikatorze w
-- logice predykatów wyższego rzędu i *jednocześnie* znasz się już trochę na programowaniu
-- funkcyjnym. I *jednocześnie* wiesz teraz pewne ważne rzeczy na temat podstaw całej matematyki, a
-- więc na temat wszystkiego, co jest formalizowalne. W dodatku możesz to wszystko ćwiczyć
-- *samodzielnie* korzystając z informacji zwrotnych dostarczanych przez Leana.

----------------------------------------------------------------------------------------------------
-- KWESTIA ISTNIENIA

-- TODO
