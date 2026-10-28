import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

/-! # Complementary Kernel Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelMap.Construction

noncomputable section

/-! A commuting group square maps one actual kernel into another.
Coprime exponents make that restricted morphism a monomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B C Z : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z]
  (r : B ⟶ A) [IsMonHom r] (q : B ⟶ C) [IsMonHom q]
  (g : C ⟶ Z) [IsMonHom g] (φ : A ⟶ Z) [IsMonHom φ]
  (h : r ≫ φ = q ≫ g)

include h

def complementaryKernelMap : Picard.PoincareBundle.Kernel.Scheme.kernelObject r ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject g :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv g _).symm ⟨Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ q, by
    change (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ q) ≫ g = 1
    rw [Category.assoc, ← h, ← Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.one_comp]⟩

omit [IsMonHom q] in
theorem complementaryKernelMap_inclusion :
    complementaryKernelMap r q g φ h ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ q :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

instance complementaryKernelMap_isMonHom : IsMonHom (complementaryKernelMap r q g φ h) := by
  have : IsMonHom (complementaryKernelMap r q g φ h ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g) := by
    rw [complementaryKernelMap_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion g)

include h in
theorem complementaryKernelMap_mono [IsCommMonObj B] (n d : ℕ) (hnd : n.Coprime d)
    (hr : ∀ (T : Over S) (x : T ⟶ B), x ≫ r = 1 → x ^ n = 1)
    (hq : ∀ (T : Over S) (x : T ⟶ B), x ≫ q = 1 → x ^ d = 1) :
    Mono (complementaryKernelMap r q g φ h) := by
  constructor
  intro T x y hxy
  let b := (x / y) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r
  have hrb : b ≫ r = 1 := by rw [Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  have hqb : b ≫ q = 1 := by
    change ((x / y) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) ≫ q = 1
    rw [Category.assoc, ← complementaryKernelMap_inclusion r q g φ h, ← Category.assoc,
      GrpObj.div_comp, hxy, div_self', MonObj.one_comp]
  have hb : b = 1 := Picard.PoincareBundle.CoprimeKernels.eq_one_of_coprime_powers n d hnd b (hr T b hrb) (hq T b hqb)
  apply div_eq_one.mp
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r)).mp
  exact hb.trans (MonObj.one_comp (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementaryKernelMap.Construction
