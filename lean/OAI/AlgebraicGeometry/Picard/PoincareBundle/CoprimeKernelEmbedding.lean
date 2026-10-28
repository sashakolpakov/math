import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

/-! # Coprime Kernel Embedding -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernelEmbedding

noncomputable section

/-! The original polarization kernel embeds into the descended kernel using the pullback identity and coprimality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B D Z : Over S} [GrpObj A] [GrpObj B] [GrpObj D] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj D] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (f : A ⟶ B) [IsMonHom f]
  (m : B ⟶ D) [IsMonHom m] (g : D ⟶ Z) [IsMonHom g]
  (n d : ℕ) (hnd : n.Coprime d)
  (h : f ≫ m ≫ g = φ ^ n) (v : Z ⟶ D) (hv : g ≫ v = (𝟙 D) ^ n)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)

include hnd h hv hk

/-- The original kernel is killed by the descended composite on every test scheme. -/
theorem kernel_image_killed : Kernel.Scheme.kernelInclusion φ ≫ f ≫ m = 1 := by
  let r := Kernel.Scheme.kernelInclusion φ ≫ f ≫ m
  have hd : r ^ d = 1 := by
    dsimp only [r]
    rw [← MonObj.pow_comp, hk _ _ (Kernel.Scheme.kernelInclusion_comp φ), MonObj.one_comp]
  have hr : r ≫ g = 1 := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc, h, MonObj.comp_pow, Kernel.Scheme.kernelInclusion_comp, one_pow]
  have hn : r ^ n = 1 := by
    have he := congrArg (fun a => a ≫ v) hr
    rw [Category.assoc, hv, MonObj.comp_pow, Category.comp_id] at he
    have hvone : (1 : Kernel.Scheme.kernelObject φ ⟶ Z) ≫ v = 1 := by
      have ht := congrArg (fun a => (1 : Kernel.Scheme.kernelObject φ ⟶ D) ≫ a) hv
      rw [← Category.assoc, MonObj.one_comp, MonObj.comp_pow, Category.comp_id, one_pow] at ht
      exact ht
    exact he.trans hvone
  exact CoprimeKernels.eq_one_of_coprime_powers n d hnd r hn hd

/-- The quotient restricts to an actual morphism from the original kernel into the descended kernel. -/
def map : Kernel.Scheme.kernelObject φ ⟶ Kernel.Scheme.kernelObject m :=
  (Kernel.Scheme.kernelPointsEquiv m _).symm ⟨Kernel.Scheme.kernelInclusion φ ≫ f, by
    change (Kernel.Scheme.kernelInclusion φ ≫ f) ≫ m = 1
    rw [Category.assoc]
    exact kernel_image_killed φ f m g n d hnd h v hv hk⟩

/-- The original and descended subgroup inclusions commute with the quotient. -/
theorem map_inclusion :
    map φ f m g n d hnd h v hv hk ≫ Kernel.Scheme.kernelInclusion m = Kernel.Scheme.kernelInclusion φ ≫ f :=
  pullback.lift_fst _ _ _

instance map_isMonHom : IsMonHom (map φ f m g n d hnd h v hv hk) := by
  have : IsMonHom (map φ f m g n d hnd h v hv hk ≫ Kernel.Scheme.kernelInclusion m) := by
    rw [map_inclusion]
    infer_instance
  exact Kernel.Splitting.isMonHom_of_mono_postcomp _ (Kernel.Scheme.kernelInclusion m)

variable (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

include hf

omit h hv in
/-- Coprime kernels make the restriction of the quotient injective as a scheme morphism. -/
theorem inclusion_comp_mono : Mono (Kernel.Scheme.kernelInclusion φ ≫ f) := by
  constructor
  intro T x y hxy
  apply (cancel_mono (Kernel.Scheme.kernelInclusion φ)).mp
  apply div_eq_one.mp
  let z := (x ≫ Kernel.Scheme.kernelInclusion φ) / (y ≫ Kernel.Scheme.kernelInclusion φ)
  have hzf : z ≫ f = 1 := by
    dsimp only [z]
    rw [GrpObj.div_comp]
    simp only [Category.assoc, hxy, div_self']
  have hzφ : z ≫ φ = 1 := by
    dsimp only [z]
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, Kernel.Scheme.kernelInclusion_comp,
      MonObj.comp_one, MonObj.comp_one, div_self']
  exact CoprimeKernels.eq_one_of_coprime_powers n d hnd z (hf T z hzf) (hk T z hzφ)

/-- This is a monomorphism of the full represented subgroup schemes, including infinitesimal points. -/
theorem map_mono : Mono (map φ f m g n d hnd h v hv hk) := by
  have : Mono (Kernel.Scheme.kernelInclusion φ ≫ f) := inclusion_comp_mono φ f n d hnd hk hf
  constructor
  intro T x y hxy
  apply (cancel_mono (Kernel.Scheme.kernelInclusion φ ≫ f)).mp
  rw [← map_inclusion φ f m g n d hnd h v hv hk, ← Category.assoc, ← Category.assoc, hxy]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernelEmbedding
