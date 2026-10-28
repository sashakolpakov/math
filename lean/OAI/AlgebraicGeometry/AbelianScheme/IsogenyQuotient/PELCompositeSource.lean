import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange

/-! # PEL Composite Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Coherent source transport through two successive base changes.
The complete PEL comparison retains the actual original point map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem PELCompositeSource.Construction.abelianPullbackCompIso_hom_source
    {S S' S'' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.pullbackCompIso f h).hom.left ≫ pullback.fst (A.pullback f).scheme.hom h ≫
      pullback.fst A.scheme.hom f = pullback.fst A.scheme.hom (h ≫ f) := by
  let e := A.pullbackCompIso f h
  have hi : e.inv.left ≫ pullback.fst A.scheme.hom (h ≫ f) =
      pullback.fst (A.pullback f).scheme.hom h ≫ pullback.fst A.scheme.hom f :=
    A.pullbackCompIso_inv_left_fst f h
  have he : e.hom.left ≫ e.inv.left = 𝟙 _ := congrArg Over.Hom.left e.hom_inv_id
  change e.hom.left ≫ _ = _
  rw [← hi, ← Category.assoc, he, Category.id_comp]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T U V : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (f : U ⟶ T) (h : V ⟶ U) (g : V ⟶ T) (hg : h ≫ f = g)

def PELCompositeSource.Construction.pelCompositeSourceIso : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso (A.pullback g) ((A.pullback f).pullback h) := by
  subst g
  exact AbelianModuli.ReferenceFamily.PEL.Objects.PELIso.pullbackComp A f h

theorem PELCompositeSource.Construction.pelCompositeSourceIso_original_point :
    (PELCompositeSource.Construction.pelCompositeSourceIso A f h g hg).polarized.abelian.hom.left ≫
      pullback.fst (A.polarized.abelian.pullback f.left).scheme.hom h.left ≫
        pullback.fst A.polarized.abelian.scheme.hom f.left =
      pullback.fst A.polarized.abelian.scheme.hom g.left := by
  subst g
  exact PELCompositeSource.Construction.abelianPullbackCompIso_hom_source A.polarized.abelian f.left h.left

def Intrinsic.PELBaseChange.Construction.NativePELQuotient.pullbackCompositeSource {B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N U}
    (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient (A.pullback f) B n) : Intrinsic.PELBaseChange.Construction.NativePELQuotient (A.pullback g) (B.pullback h) n :=
  (r.pullback h).precompose (PELCompositeSource.Construction.pelCompositeSourceIso A f h g hg)

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.pullbackCompositeSource_hom {B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N U}
    (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient (A.pullback f) B n) :
    (r.pullbackCompositeSource A f h g hg).isogeny.hom =
      (PELCompositeSource.Construction.pelCompositeSourceIso A f h g hg).polarized.abelian.hom ≫ (r.isogeny.pullback h.left).hom := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
