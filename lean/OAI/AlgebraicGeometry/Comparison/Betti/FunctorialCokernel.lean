import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functorial Cokernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel.Resolution

noncomputable section

/-! The actual cokernel of a natural map into an additive endofunctor
is itself an additive functor, with its canonical short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (T : C ⥤ C) (η : 𝟭 C ⟶ T)

def quotientFunctor : C ⥤ C where
  obj X := cokernel (η.app X)
  map {X Y} f := cokernel.map (η.app X) (η.app Y) f (T.map f) (η.naturality f).symm
  map_id X := by
    apply (cancel_epi (cokernel.π (η.app X))).mp
    simp only [cokernel.map, cokernel.π_desc, T.map_id, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (cokernel.π (η.app _))).mp
    simp only [cokernel.map, cokernel.π_desc, cokernel.π_desc_assoc, T.map_comp, Category.assoc]

instance quotientFunctor_additive [T.Additive] : (quotientFunctor T η).Additive where
  map_add {X Y} f g := by
    apply (cancel_epi (cokernel.π (η.app X))).mp
    change cokernel.π (η.app X) ≫ cokernel.map (η.app X) (η.app Y) (f + g) (T.map (f + g))
        (η.naturality (f + g)).symm =
      cokernel.π (η.app X) ≫
        (cokernel.map (η.app X) (η.app Y) f (T.map f) (η.naturality f).symm +
          cokernel.map (η.app X) (η.app Y) g (T.map g) (η.naturality g).symm)
    simp only [Preadditive.comp_add, cokernel.map, cokernel.π_desc, T.map_add, Preadditive.add_comp]

def quotientProjection : T ⟶ quotientFunctor T η where
  app X := cokernel.π (η.app X)
  naturality {X _Y} _f := (cokernel.π_desc (η.app X) _ _).symm

theorem unit_projection_zero (X : C) : η.app X ≫ (quotientProjection T η).app X = 0 :=
  cokernel.condition (η.app X)

def quotientShortComplex (X : C) : ShortComplex C :=
  ShortComplex.mk (η.app X) ((quotientProjection T η).app X) (unit_projection_zero T η X)

theorem quotientShortComplex_shortExact (X : C) [Mono (η.app X)] :
    (quotientShortComplex T η X).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (η.app X))
  mono_f := inferInstanceAs (Mono (η.app X))
  epi_g := inferInstanceAs (Epi (cokernel.π (η.app X)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel.Resolution
