import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactConeKernel
import Mathlib.Algebra.Homology.SingleHomology

/-! # Dual Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualPurity

noncomputable section

/-! Purity of the ordinary dual of the actual finite Koszul resolution.
The proof uses regular multiplication on successive quotients, viewed as
an epimorphism in the opposite module category. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u
variable (R : Type u) [CommRing R]

abbrev single := HomologicalComplex.single (ModuleCat.{u} R)ᵒᵖ (.up ℤ) 0
abbrev Q (rs : List R) := RegularSequenceKoszul.quotient (ModuleCat.of R R) rs
abbrev K (rs : List R) := RegularSequenceKoszul.complex (ModuleCat.of R R) rs
abbrev D (rs : List R) := DualFunctor.complex R (K R rs)

theorem single_scalar (M : (ModuleCat.{u} R)ᵒᵖ) (r : R) :
    (DualPurity.single R).map (r • 𝟙 M) = r • 𝟙 ((DualPurity.single R).obj M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _

def shiftedSequence (M : ModuleCat.{u} R) (r : R) (c : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R)ᵒᵖ ℤ) :=
  (((RegularElementKoszul.sequence M r).op).map (DualPurity.single R)).map
    (shiftFunctor (CochainComplex (ModuleCat.{u} R)ᵒᵖ ℤ) c)

theorem shiftedSequence_shortExact (M : ModuleCat.{u} R) (r : R) (c : ℤ)
    (hr : IsSMulRegular M r) : (shiftedSequence R M r c).ShortExact :=
  (((RegularElementKoszul.sequence_shortExact M r hr).op).map_of_exact (DualPurity.single R)).map_of_exact _

theorem shiftedSequence_g (M : ModuleCat.{u} R) (r : R) (c : ℤ) :
    (shiftedSequence R M r c).g = r • 𝟙 (((DualPurity.single R).obj (op M))⟦c⟧) := by
  change (shiftFunctor _ c).map ((DualPurity.single R).map
    (ModuleCat.ofHom (r • (LinearMap.id : M →ₗ[R] M))).op) = _
  change (shiftFunctor _ c).map ((DualPurity.single R).map (r • 𝟙 (op M))) = _
  rw [single_scalar]
  rfl

def dualRingIso : (DualFunctor.functor R).obj (ModuleCat.of R R) ≅
    op (ModuleCat.of R R) :=
  (LinearMap.ringLmapEquivSelf R R R).symm.toModuleIso.op

def nilIso : D R [] ≅ (DualPurity.single R).obj (op (Q R [])) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (DualFunctor.functor R) (.up ℤ) 0).app (ModuleCat.of R R) ≪≫
      (DualPurity.single R).mapIso (dualRingIso R) ≪≫
        (DualPurity.single R).mapIso (RegularSequenceKoszul.quotientNilIso (ModuleCat.of R R)).op

theorem exists_comparison (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :
    ∃ ε : ((DualPurity.single R).obj (op (Q R rs)))⟦(rs.length : ℤ)⟧ ⟶ D R rs, QuasiIso ε := by
  induction rs using List.reverseRecOn with
  | nil =>
    refine ⟨(shiftFunctorZero _ ℤ).hom.app _ ≫ (nilIso R).inv, ?_⟩
    infer_instance
  | append_singleton rs r ih =>
    obtain ⟨hprev, hlast⟩ := (RingTheory.Sequence.isWeaklyRegular_append_iff R rs [r]).mp hreg
    have hr := (RingTheory.Sequence.isWeaklyRegular_singleton_iff (Q R rs) r).mp hlast
    obtain ⟨ε, hε⟩ := ih hprev
    let c : ℤ := rs.length
    let S := shiftedSequence R (Q R rs) r c
    have hS := shiftedSequence_shortExact R (Q R rs) r c hr
    let eQ := RegularSequenceKoszul.quotientAppendIso (ModuleCat.of R R) rs r
    let A := (DualPurity.single R).obj (op (ModuleCat.of R (QuotSMulTop r (Q R rs))))
    let sourceIso : ((DualPurity.single R).obj (op (Q R (rs ++ [r]))))⟦((rs ++ [r]).length : ℤ)⟧ ≅
        S.X₁⟦(1 : ℤ)⟧ :=
      (shiftFunctor _ ((rs ++ [r]).length : ℤ)).mapIso ((DualPurity.single R).mapIso eQ.op.symm) ≪≫
        (shiftFunctorAdd' _ c 1 ((rs ++ [r]).length : ℤ) (by simp [c])).app A
    let b : CochainComplex.mappingCone S.g ⟶
        CochainComplex.mappingCone (r • 𝟙 (D R rs)) :=
      CochainComplex.mappingCone.map _ _ ε ε (by
        rw [shiftedSequence_g]
        apply HomologicalComplex.Hom.ext
        funext i
        apply Quiver.Hom.unop_inj
        apply ModuleCat.hom_ext
        ext x
        exact ((ε.f i).unop.hom.map_smul r x).symm)
    have hb : QuasiIso b := PeriodInvariants.MappingConeQuasiIso.quasiIso_map _ _ ε ε _ hε hε
    have hc := ShortExactConeKernel.comparison_quasiIso S hS
    have he : D R (rs ++ [r]) ≅ CochainComplex.mappingCone (r • 𝟙 (D R rs)) :=
      eqToIso (by rw [D, K, RegularSequenceKoszul.complex_append_singleton]) ≪≫
        DualFunctor.coneIso R (K R rs) r
    exact ⟨sourceIso.hom ≫ ShortExactConeKernel.comparison S ≫ b ≫ he.inv, inferInstance⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualPurity
