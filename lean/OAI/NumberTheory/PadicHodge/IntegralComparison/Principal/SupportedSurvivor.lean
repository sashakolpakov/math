import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction

/-! # Supported Survivor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedSurvivor

noncomputable section

/-! The original closed survivor controls the support concentration
on the entire native principal diagram. Positive parameter intersections
vanish by the genuine closed support, rather than a supplied zero-row premise. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsClosedImmersion f]
  (N : Z.Modules) (S : Y.Modules) (e : S ≅ (Scheme.Modules.pushforward f).obj N)
  (U : Y.Opens) (hU : IsAffineOpen U)

include e in
theorem sections_zero (r : SectionPresheaf.Index U)
    (hr : SectionPresheaf.openSubset U r ≤ SectionIdealPuncturedCover.outside f.ker) :
    IsZero ((SectionPresheaf.modules U hU S).obj (op r)) := by
  have hempty : f ⁻¹ᵁ SectionPresheaf.openSubset U r = ⊥ :=
    le_antisymm ((f.preimage_mono hr).trans (Closed.SupportedSurvivor.preimage_outside f).le) bot_le
  let : Subsingleton Γ(Z, f ⁻¹ᵁ SectionPresheaf.openSubset U r) := by rw [hempty]; infer_instance
  have hk : RingHom.ker (f.app (SectionPresheaf.openSubset U r)).hom = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ (x := 1) _ isUnit_one
    change f.app _ 1 = 0
    exact Subsingleton.elim _ _
  have hz := (Projective.ComplementAdjunction.directImage_sections_zero f N (SectionPresheaf.openSubset U r) hk).of_iso
    ((Affine.ModuleExactSections.sections (SectionPresheaf.openSubset U r)).mapIso e)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton Γ(S, SectionPresheaf.openSubset U r)
  exact ModuleCat.isZero_iff_subsingleton.mp hz

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (hW : ∀ i, SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

include e hW in
theorem intersection_zero (q : ℕ) (hq : 0 < q) (a : AugmentedOrdered.Cech.Index ι q) :
    IsZero ((SectionPresheaf.modules U hU S).obj (op ((AugmentedOrdered.Cech.formal W q).obj a))) := by
  let j : Fin q := ⟨0, hq⟩
  let p : (AugmentedOrdered.Cech.formal W q).obj a ⟶ W (a.val j) := Pi.π _ j
  exact sections_zero f N S e U hU _ ((SectionPresheaf.arrow U hU p).le.trans (hW (a.val j)))

variable (K : CochainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (eK : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)

abbrev complex := ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj K

include N eK hW in
theorem homology_zero (q : ℕ) (hq : 0 < q) (a : AugmentedOrdered.Cech.Index ι q) :
    IsZero (((complex U hU K).homology c).obj (op ((AugmentedOrdered.Cech.formal W q).obj a))) :=
  (intersection_zero f N (K.homology c) eK U hU W hW q hq a).of_iso
    ((ModuleHomology.complexIso U hU K c).app (op ((AugmentedOrdered.Cech.formal W q).obj a)))

include N eK hW in
theorem terms_zero (p q : ℕ) (hq : 0 < q) (a : AugmentedOrdered.Cech.Index ι q) :
    IsZero ((((single _ (.up ℕ) c).obj ((complex U hU K).homology c)).X p).obj
      (op ((AugmentedOrdered.Cech.formal W q).obj a))) := by
  let E := (CategoryTheory.evaluation (SectionPresheaf.Index U)ᵒᵖ
    (ModuleCat Γ(Y, U))).obj (op ((AugmentedOrdered.Cech.formal W q).obj a))
  by_cases hp : p = c
  · subst p
    exact (homology_zero f N U hU W hW K c eK q hq a).of_iso
      (E.mapIso (singleObjXSelf (.up ℕ) c ((complex U hU K).homology c)))
  · exact E.map_isZero (isZero_single_obj_X (.up ℕ) c ((complex U hU K).homology c) p hp)

variable (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev concentration := AugmentedCech.Concentration.iso W (complex U hU K) c
  (fun q hq => ModuleHomology.exactAt U hU K q (hK q hq))

abbrev lift_normalization := Supported.ConcentrationForget.lift_normalization W (complex U hU K) c
  (fun q hq => ModuleHomology.exactAt U hU K q (hK q hq))
  (terms_zero f N U hU W hW K c eK)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedSurvivor
