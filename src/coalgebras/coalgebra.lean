import ..functors.functor

namespace category_theory

structure coalgebra {C: category} (F : functor C C) :=
(object : C.C₀)
(morphism : C.hom object (F.map_obj object))

structure f_coalgebra_homomorphism {C : category} {F : functor C C} (A B : coalgebra F) :=
  (morphism : C.hom A.object B.object)
  (proof : C.compose B.morphism morphism = C.compose (F.map_hom morphism) A.morphism) 

end category_theory
