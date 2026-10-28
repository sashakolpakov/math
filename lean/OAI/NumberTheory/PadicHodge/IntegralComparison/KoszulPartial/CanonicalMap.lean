import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

/-! # Canonical Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap

noncomputable section

/-! Forgetting the support in the mixed partial-fraction map is the
canonical contravariant quotient map on Ext, followed by scalar extension
of its values. This normalization holds on the actual cochain maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def scalarsMap : DualComplexHomology.complex R (Koszul.OrientedTopCohomology.koszul R s) ⟶
    AugmentedOrdered.CechForget.ambientComplex (Components.coefficient R P s) where
  f n := ModuleCat.ofHom
    { toFun := fun φ => (Algebra.linearMap R (P.obj (op (⊤_ C)))).comp φ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp [Algebra.smul_def] }
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change Module.Dual R (⋀[R]^i (Fractions.normal R (c := c))) at φ
    dsimp only [DualComplexHomology.complex, Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.op_d, ExactModuleDualFunctor.functor]
    symm
    change algebraMap R (P.obj (op (⊤_ C)))
      (φ ((Koszul.OrientedTopCohomology.koszul R s).d (i + 1) i x)) =
        (show (⋀[R]^(i + 1) (Fractions.normal R (c := c))) →ₗ[R] P.obj (op (⊤_ C)) from
          ((Components.coefficient R P s).d i (i + 1)).app (op (⊤_ C))
            ((Algebra.linearMap R (P.obj (op (⊤_ C)))).comp φ)) x
    rw [Exterior.KoszulHomotopy.complex_d]
    change _ = (show (⋀[R]^(i + 1) (Fractions.normal R (c := c))) →ₗ[R] P.obj (op (⊤_ C)) from
      ((Koszul.HomPresheaf.complex R (Fractions.normal R (c := c)) (Fractions.modules R P)
        (Koszul.GeneratorMatrix.equation R s)).d i (i + 1)).app _ _) x
    dsimp only [Koszul.HomPresheaf.complex]
    rw [CochainComplex.of_d]
    rfl

theorem forget_factorization : Forget.ambientMap R P U s t ht =
    DualComplexHomology.map R (Resolution.inclusion R s t) ≫ scalarsMap R P s := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact Forget.ambientMap_apply R P U s t ht n φ x

theorem canonical_map
    (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
    (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t))) (n : ℕ) :
    homologyMap (Forget.ambientMap R P U s t ht) n =
      Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
        (Resolution.normalResolution R s hs)
        (Resolution.pointResolution R s t hst)
        (Resolution.quotient R s t) n ≫ homologyMap (scalarsMap R P s) n := by
  rw [forget_factorization, homologyMap_comp,
    Resolution.canonical_map R s t (ExactModuleDualFunctor.functor R) hs hst n]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap
