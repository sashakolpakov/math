import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeTransport

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Transport every component of polarized full-level data along a family isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

/-- Transport dual, polarization, and ordered level to an isomorphic abelian scheme. -/
def PolarizationData.PolarizedAbelianWithFullLevel.familyTransport (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {B : Abelian.Schemes.AbelianScheme g S}
    (e : A.abelian.scheme ≅ B.scheme) [IsMonHom e.hom] :
    PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := B
  dual := A.dual.familyTransport e
  polarization := A.polarization.familyTransport e
  level := A.level.transport e

/-- The transported full moduli object is isomorphic to the original one. -/
def PolarizationData.PolarizedAbelianWithFullLevel.familyTransportIso (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {B : Abelian.Schemes.AbelianScheme g S}
    (e : A.abelian.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Moduli.Isomorphisms.LevelPreservingIso A (A.familyTransport e) where
  abelian := e
  dual := Iso.refl A.dual.abelian.scheme
  abelianGroup := inferInstanceAs (IsMonHom e.hom)
  dualGroup := inferInstanceAs (IsMonHom (𝟙 A.dual.abelian.scheme))
  polarization := by
    change A.polarization.isogeny.hom ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ A.polarization.isogeny.hom)
    simp only [Category.comp_id, e.hom_inv_id_assoc]
  poincare := by
    let p := (Over.forget S).mapIso (Iso.refl A.dual.abelian.scheme ⊗ᵢ e)
    exact (Line.Bundles.LineBundle.pullbackIso p).right_inv (Line.Bundles.LineBundle.classOf A.dual.poincare)
  level _ _ := rfl

/-- Transport the abelian group structure as well, starting with a scheme isomorphism. -/
def PolarizationData.PolarizedAbelianWithFullLevel.transportAlong (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {Z : Over S}
    (e : A.abelian.scheme ≅ Z) : PolarizationData.PolarizedAbelianWithFullLevel g δ N S :=
  A.familyTransport (A.abelian.transportIso e)

/-- All structures on an isomorphic underlying scheme give the same moduli class. -/
def PolarizationData.PolarizedAbelianWithFullLevel.transportAlongIso (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {Z : Over S}
    (e : A.abelian.scheme ≅ Z) : Moduli.Isomorphisms.LevelPreservingIso A (A.transportAlong e) :=
  A.familyTransportIso (A.abelian.transportIso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
