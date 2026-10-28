import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # Iso Preimages -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsoPreimages

noncomputable section

/-! A group isomorphism preserves the actual integral Tate image,
so postcomposing an isogeny with it does not change its preimage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B C : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
  (T : Over S) (q : ℕ) [Fact q.Prime]

theorem isogenyTatePreimage_iso (e : A ≅ B) [IsMonHom e.hom] :
    Rational.isogenyTatePreimage (T := T) (q := q) e.hom = Rational.integralTateImage A T q := by
  apply le_antisymm
  · have h := Lattices.isogenyTatePreimage_mono_comp T q e.hom e.inv
    simpa only [e.hom_inv_id, Lattices.isogenyTatePreimage_id] using h
  · exact Lattices.integralTateImage_le_preimage T q e.hom

theorem isogenyTatePreimage_comp_iso (f : A ⟶ B) [IsMonHom f] (e : B ≅ C) [IsMonHom e.hom] :
    Rational.isogenyTatePreimage (T := T) (q := q) (f ≫ e.hom) =
      Rational.isogenyTatePreimage (T := T) (q := q) f := by
  rw [Lattices.isogenyTatePreimage_comp, isogenyTatePreimage_iso]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsoPreimages
