import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Finite Group Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation

noncomputable section

/-! Finite commutative group schemes over a field have actual affine
presentations in FiniteEtale's format. This is a presentation theorem, with
finiteness supplied by the geometric torsion theorem when it is available. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

section TorsionPresentation

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def torsionEqualizerRepresentable (m : ℕ) :
    (A.torsionFunctor m ⋙ forget GrpCat).RepresentableBy (BlocksProjectors.torsionScheme A m) where
  homEquiv := BlocksProjectors.torsionPointsEquiv A m _
  homEquiv_comp f x := Subtype.ext (Category.assoc f x _)

/-- The equalizer and zero-fiber constructions represent the same torsion functor. -/
def torsionEqualizerIso (m : ℕ) : BlocksProjectors.torsionScheme A m ≅ A.torsionScheme m :=
  (torsionEqualizerRepresentable A m).uniqueUpToIso (A.torsionRepresentable m)

theorem torsionEqualizer_finite (m : ℕ) [IsFinite (A.torsionScheme m).hom] :
    IsFinite (BlocksProjectors.torsionScheme A m).hom := by
  let e := torsionEqualizerIso A m
  have : IsIso e.hom.left := inferInstanceAs
    (IsIso (((Over.forget S).mapIso e).hom))
  rw [← e.hom.w]
  infer_instance

theorem idempotentBlock_finite {O : Type} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (m : ℕ) (e : O)
    [IsFinite (A.torsionScheme m).hom] :
    IsFinite (BlocksProjectors.idempotentBlockScheme A ρ m e).hom := by
  let : IsFinite (BlocksProjectors.torsionScheme A m).hom := torsionEqualizer_finite A m
  let i := equalizer.ι (BlocksProjectors.torsionInclusion A m ≫ ρ.map e) (BlocksProjectors.torsionInclusion A m)
  have : IsClosedImmersion i.left := isClosedImmersion_equalizer_ι_left _ _
  rw [← i.w]
  infer_instance

end TorsionPresentation

theorem finite_group_affine_presentation
    {k : Type} [Field k]
    (G : CommGrp (Over (Spec (.of k)))) [IsFinite G.X.hom] :
    ∃ H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k,
      ∃ e : H.scheme ≅ G.X, IsMonHom e.hom := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k) (G := G.X)).mpr
    (inferInstanceAs (IsAffine G.X.left))
  let : GrpObj (GroupSchemes.FiniteEtale.affine k R.unop) := GrpObj.ofIso e.symm
  have hinv : IsMonHom e.symm.hom := isMonHom_ofIso e.symm
  let : IsMonHom e.inv := hinv
  have hhom : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  let : IsMonHom e.hom := hhom
  have hcomm : IsCommMonObj (GroupSchemes.FiniteEtale.affine k R.unop) := by
    apply (isCommMonObj_iff_isMulCommutative _).mpr
    intro T
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (cancel_mono e.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  let : IsCommMonObj (GroupSchemes.FiniteEtale.affine k R.unop) := hcomm
  have hfinite : IsFinite (GroupSchemes.FiniteEtale.affine k R.unop).hom := by
    rw [← e.hom.w]
    have : IsIso e.hom.left := inferInstanceAs
      (IsIso (((Over.forget (Spec (.of k))).mapIso e).hom))
    infer_instance
  have hmodule : Module.Finite k R.unop := by
    apply RingHom.finite_algebraMap.mp
    exact (IsFinite.SpecMap_iff _).mp hfinite
  let H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k := {
    algebra := R.unop
    finite := hmodule
    group := { toGrpObj := inferInstance, toIsCommMonObj := inferInstance } }
  exact ⟨H, e, hhom⟩

/-- Each finite character block has a genuine FiniteEtale finite-group presentation. -/
theorem split_block_affine_presentation
    {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (n : ℕ) (τ : Gal(E/ℚ)) [IsFinite (A.torsionScheme (q ^ n)).hom] :
    ∃ H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k,
      ∃ e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X,
        IsMonHom e.hom := by
  let G := BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ
  have : IsFinite G.X.hom :=
    idempotentBlock_finite A ρ (q ^ n) (j.projector iota hsplit n τ)
  exact finite_group_affine_presentation G

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation
