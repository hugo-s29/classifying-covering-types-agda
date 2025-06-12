#set page(width: auto)

= Naming conventions: HoTT Book _vs_ Agda Cubical.


#let header(it) = align(center, strong(smallcaps(it)))
#show sym.eq : math.scripts

#table(
  columns: (auto, auto, auto),
  header[],
  header[In the HoTT Book],
  header[In Agda Cubical],
  emph[Path between],
  [$x =_A y$],
  [`x ≡ y` (the `A` is implicit in `≡`)],
  emph[Action on paths],
  $sans("ap")_f : x =_A y -> f(x) =_B f(y)$,
  [`cong : (f : A → B) → x ≡ y → f x ≡ f y` #footnote[Works with dependent paths too]],
  emph[Transport],
  [$sans("transport")_P : x =_A y -> P(x) -> P(y)$ where $P : A -> cal(U)$],
  `subst : (P : A → Type) → x ≡ y → P x → P y`
)
