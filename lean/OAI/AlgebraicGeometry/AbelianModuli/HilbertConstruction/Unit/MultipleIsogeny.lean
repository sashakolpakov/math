import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GroupDivisionLocus

/-! # Multiple Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplying the source of an isogeny by an invertible integer gives
the exact composite isogeny, and preserves etaleness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))

def Abelian.Schemes.AbelianScheme.Isogeny.unitMultiple : Abelian.Schemes.AbelianScheme.Isogeny A B := by
  have hg := Unit.GroupDivisionLocus.unit_multiplication_geometry A n hn
  let : IsFinite (A.multiplication n).left := hg.1
  let : Flat (A.multiplication n).left := hg.2.1
  let : Surjective (A.multiplication n).left := hg.2.2.1
  let : IsMonHom (A.multiplication n) := by
    rw [← A.endRing_natCast_hom n]
    infer_instance
  exact
    { hom := A.multiplication n ≫ p.hom
      preservesGroup := inferInstance
      finite := inferInstanceAs (IsFinite ((A.multiplication n).left ≫ p.hom.left))
      flat := inferInstanceAs (Flat ((A.multiplication n).left ≫ p.hom.left))
      surjective := inferInstanceAs (Surjective ((A.multiplication n).left ≫ p.hom.left)) }

theorem Abelian.Schemes.AbelianScheme.Isogeny.unitMultiple_hom : (p.unitMultiple n hn).hom = A.multiplication n ≫ p.hom := rfl

instance Abelian.Schemes.AbelianScheme.Isogeny.unitMultiple_etale [Etale p.hom.left] : Etale (p.unitMultiple n hn).hom.left := by
  let : Etale (A.multiplication n).left := (Unit.GroupDivisionLocus.unit_multiplication_geometry A n hn).2.2.2.2
  exact inferInstanceAs (Etale ((A.multiplication n).left ≫ p.hom.left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
