import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation

/-! # Top Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone

noncomputable section

/-! The original top-section restriction is a cone of presheaf
complexes, before choosing a Cech covering family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u a b
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {A : Type a} [Category.{b} A] [Abelian A]

def global : CochainComplex (Cᵒᵖ ⥤ A) ℕ ⥤ CochainComplex A ℕ :=
  (((evaluation Cᵒᵖ A).obj (op ⊤)).mapHomologicalComplex (.up ℕ))

def cone (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (ConeTotal.CechPresheafConeTotal.constant (C := C)).obj ((global C).obj K) ⟶ K where
  f q := Semilattice.CechAugmentation.SemilatticeCechAugmentation.cone C (K.X q)
  comm' q q' _ := by
    apply NatTrans.ext
    funext V
    exact (K.d q q').naturality (homOfLE (le_top : V.unop ≤ ⊤)).op

theorem naturality {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (α : K ⟶ L) :
    cone C K ≫ α = (ConeTotal.CechPresheafConeTotal.constant (C := C)).map ((global C).map α) ≫ cone C L := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext V
  exact (α.f q).naturality (homOfLE (le_top : V.unop ≤ ⊤)).op

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone
