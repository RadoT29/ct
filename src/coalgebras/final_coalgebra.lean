import .coalgebras_category

namespace category_theory

structure final_coalgebra {C : category} (F : functor C C) :=
  (obj : coalgebra F)
  (anamorphism : Π (A : coalgebra F), (coalgebra_category F).hom A obj)
  (unique :  ∀ {A : (coalgebra_category F).C₀} (f : (coalgebra_category F).hom A obj), f = anamorphism A)

-- theorem id_property {C : category} (F : functor C C) (A : final_coalgebra F) : A.obj.id

-- theorem theorem207 {C : category} (F : functor C C) (A B : coalgebra F) (v : final_coalgebra F) : C.compose B.morphism (f_coalgebra_homomorphism A B) :=

end category_theory