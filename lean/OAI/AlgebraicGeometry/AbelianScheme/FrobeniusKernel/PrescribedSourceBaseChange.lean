import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport

/-! # Prescribed Source Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceBaseChange.Construction

noncomputable section

/-! The exact full-kernel comparison combines native field base change
with a full polarized source isomorphism. Intermediate chosen subgroups
are constructed by transport, retaining their finite Cartier coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k')))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
variable (s : Spec (.of k') ⟶ Spec (.of k))
variable (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback s) B)
variable (he : ∀ z : NumberField.RingOfIntegers E,
  (ρ.pullback s).map z ≫ e.abelian.hom = e.abelian.hom ≫ σ.map z)
variable (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (J : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k' (CMPointsAt.Construction.l45ChosenBlock j iota hsplit B σ (labels (v, false)) n))
variable (eH : ∀ v, (Over.pullback s).obj (H v).group.X ≅ (J v).group.X)
variable (heH : ∀ v, (eH v).hom ≫ (J v).inclusion.hom.hom =
  (Over.pullback s).map (H v).inclusion.hom.hom ≫
    (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n (labels (v, false))).hom.hom.hom ≫
      (PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit (A.pullback s).abelian B.abelian (ρ.pullback s) σ
        e.abelian.hom he n (labels (v, false))).hom.hom)

include heH in
theorem prescribedFullKernel_sourceBaseChange (Q : Over (Spec (.of k')))
    (a : Q ⟶ (A.pullback s).abelian.scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit B σ n r labels J Q (a ≫ e.abelian.hom) ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H ((Over.map s).obj Q)
        (A.abelian.baseChangePointsMulEquiv s Q a) := by
  let b v := IntrinsicBlockSourceIso.Construction.l45NativeBlockSourceIso j iota hsplit (A.pullback s).abelian B.abelian
    (ρ.pullback s) σ e.abelian he n (labels (v, false))
  let bi v := (Grp.forget (Over (Spec (.of k')))).mapIso (b v)
  let I v := (J v).transport (b v).symm
  have hi : ∀ v, (eH v).hom ≫ (I v).inclusion.hom.hom =
      (Over.pullback s).map (H v).inclusion.hom.hom ≫
        (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n (labels (v, false))).hom.hom.hom := by
    intro v
    have hh : (eH v).hom ≫ (J v).inclusion.hom.hom =
        (Over.pullback s).map (H v).inclusion.hom.hom ≫
          (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n (labels (v, false))).hom.hom.hom ≫
            (bi v).hom := heH v
    change (eH v).hom ≫ ((J v).inclusion.hom.hom ≫ (bi v).inv) = _
    let c := (Over.pullback s).map (H v).inclusion.hom.hom ≫
      (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n (labels (v, false))).hom.hom.hom
    have hh' : (eH v).hom ≫ (J v).inclusion.hom.hom = c ≫ (bi v).hom :=
      hh.trans (Category.assoc _ _ (bi v).hom).symm
    exact (Category.assoc (eH v).hom (J v).inclusion.hom.hom (bi v).inv).symm.trans
      ((congrArg (fun z => z ≫ (bi v).inv) hh').trans
        ((Category.assoc c (bi v).hom (bi v).inv).trans
          ((congrArg (fun z => c ≫ z) (bi v).hom_inv_id).trans (Category.comp_id c))))
  have hs : ∀ v, (Iso.refl (J v).group.X).hom ≫ (J v).inclusion.hom.hom =
      (I v).inclusion.hom.hom ≫
        (PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit (A.pullback s).abelian B.abelian (ρ.pullback s) σ
          e.abelian.hom he n (labels (v, false))).hom.hom := by
    intro v
    change (𝟙 _) ≫ (J v).inclusion.hom.hom =
      ((J v).inclusion.hom.hom ≫ (bi v).inv) ≫ (bi v).hom
    exact (Category.id_comp (J v).inclusion.hom.hom).trans
      ((Category.assoc (J v).inclusion.hom.hom (bi v).inv (bi v).hom).trans
        ((congrArg (fun z => (J v).inclusion.hom.hom ≫ z) (bi v).inv_hom_id).trans
          (Category.comp_id (J v).inclusion.hom.hom))).symm
  exact (PrescribedSourceIso.Construction.prescribedFullKernel_sourceIso j iota hsplit (A.pullback s) B (ρ.pullback s) σ
    e he n r labels I J (fun v => Iso.refl (J v).group.X) hs Q a).trans
      (PrescribedBaseChange.Construction.prescribedFullKernel_baseChange j iota hsplit A ρ s n r labels H I eH hi Q a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceBaseChange.Construction
