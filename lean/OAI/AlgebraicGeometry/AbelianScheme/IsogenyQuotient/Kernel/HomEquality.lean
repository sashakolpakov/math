import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageExactness
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Hom Equality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.HomEquality.Construction

noncomputable section

/-! Equality of the ambient homomorphisms identifies their actual
kernel group schemes and preserves the original inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g)

def kernelHomEqualityIso : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject g := by
  subst g
  exact Iso.refl _

omit [IsMonHom f] in
theorem kernelHomEqualityIso_inclusion :
    (kernelHomEqualityIso f g h).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f := by
  subst g
  exact Category.id_comp _

instance kernelHomEqualityIso_isMonHom : IsMonHom (kernelHomEqualityIso f g h).hom := by
  subst g
  exact inferInstanceAs (IsMonHom (𝟙 (Picard.PoincareBundle.Kernel.Scheme.kernelObject f)))

variable [IsCommMonObj A]
  (r : B ⟶ A) [IsMonHom r] (n : ℕ) (hfr : f ≫ r = (𝟙 A) ^ n)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

omit g h [IsMonHom g] in
theorem kernelPreimageInclusion_torsion_transport :
    PreimageExactness.Construction.kernelPreimageInclusion f r ≫ (kernelHomEqualityIso (f ≫ r) ((𝟙 A) ^ n) hfr).hom =
      Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf := by
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n))).mp
  rw [Category.assoc, kernelHomEqualityIso_inclusion, PreimageExactness.Construction.kernelPreimageInclusion_inclusion,
    Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap_inclusion]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.HomEquality.Construction
