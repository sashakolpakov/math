import Mathlib.Algebra.Homology.QuasiIso

/-! # Quasi Iso Left -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoLeft.QuasiIsoComposeIsomorphism

noncomputable section

/-! An explicit isomorphism hypothesis gives quasi-isomorphism of a composite. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M : CochainComplex C ℕ} (f : K ⟶ L) (g : L ⟶ M)

theorem left (hf : IsIso f) (hg : QuasiIso g) : QuasiIso (f ≫ g) := by
  let := hf
  let := hg
  infer_instance

theorem mappedLeft {D : Type*} [Category D] (F : D ⥤ CochainComplex C ℕ)
    {X Y : D} (a : X ⟶ Y) (b : F.obj Y ⟶ M) (ha : IsIso a) (hb : QuasiIso b) :
    QuasiIso (F.map a ≫ b) := by
  let := ha
  exact left (F.map a) b (F.map_isIso a) hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoLeft.QuasiIsoComposeIsomorphism
