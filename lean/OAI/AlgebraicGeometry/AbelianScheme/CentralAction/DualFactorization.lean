import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualPicard
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

/-! # Dual Factorization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization

noncomputable section

/-! The constructed dual quotient map reverses the actual scalar
factorization. This follows from the Poincare equations of the isogenies
and the Picard universal property, without assuming dual compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

universe u
variable {S : Scheme.{u}} {g : ℕ}

theorem poincareClass_precomp {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    {T U : Over S} (x : T ⟶ U) (f : U ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D (x ≫ f) = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map x.op (Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D f) := by
  rw [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation, D.representable.homEquiv_comp,
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation]
  exact A.homogeneousPicardSheafInclusion.hom.naturality_apply x.op (D.representable.homEquiv f)

theorem picardPullback_comp {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) :
    Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback (f ≫ g) = Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback g ≫ Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  change F.map (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf (f ≫ g)) =
    F.map (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf g) ≫ F.map (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f)
  rw [← F.map_comp]
  congr 1
  ext T q
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ (f ≫ g)).left q =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ g).left q)
  rw [whiskerLeft_comp, Over.comp_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]

variable {R : Type u} [CommRing R] {N n m : ℕ}
  {P Q Q' : TateComparison.PEL.PELFamilyData R g N S}

theorem pelIsogeny_poincareClass (f : TateComparison.PELIsogenies.PELIsogeny P Q n) :
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass P.dual f.dualHom =
      (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f.isogeny.hom).hom.app (.op Q.dual.abelian.scheme)
        (Picard.Homomorphisms.PoincareDetection.Construction.poincareClass Q.dual (𝟙 Q.dual.abelian.scheme)) := by
  rw [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply]
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard P.abelian.scheme).app (.op Q.dual.abelian.scheme))
    f.poincare.symm

/-- The dual of the quotient isomorphism is constructed, and its
factorization equation follows from the two actual PEL isogenies. -/
theorem dual_quotient_factorization
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (g : TateComparison.PELIsogenies.PELIsogeny P Q' m)
    (e : Q.abelian.scheme ≅ Q'.abelian.scheme) [IsMonHom e.hom]
    (he : f.isogeny.hom ≫ e.hom = g.isogeny.hom) :
    (DualPicard.Construction.dualUnderlyingIso Q.dual Q'.dual e).hom ≫ f.dualHom = g.dualHom := by
  let d := DualPicard.Construction.dualUnderlyingIso Q.dual Q'.dual e
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective P.dual Q'.dual.abelian.scheme
  rw [poincareClass_precomp, pelIsogeny_poincareClass, pelIsogeny_poincareClass]
  have hn := (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f.isogeny.hom).hom.naturality_apply d.hom.op
    (Picard.Homomorphisms.PoincareDetection.Construction.poincareClass Q.dual (𝟙 Q.dual.abelian.scheme))
  rw [← hn, ← poincareClass_precomp, Category.comp_id, DualPicard.Construction.dualUnderlyingIso_poincareClass]
  have hc := picardPullback_comp f.isogeny.hom e.hom
  rw [he] at hc
  rw [hc]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization
