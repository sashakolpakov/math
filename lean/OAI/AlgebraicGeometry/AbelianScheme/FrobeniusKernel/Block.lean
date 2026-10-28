import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFactorization

/-! # Block -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Block.Construction

noncomputable section

/-!
Assemble the independently proved block factorization statements and
identify the full subgroup as the actual relative Frobenius kernel.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section Products

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem groupBlockProduct_trivialFrobenius (n : ℕ) (B : Fin n → Grp (Over S))
    (hB : ∀ v, Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS (B v).X = 1) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS (BlockProducts.Construction.groupBlockProduct n B).X = 1 := by
  induction n with
  | zero =>
    let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS (Grp.trivial (Over S)).X
    have h : (𝟙 (Grp.trivial (Over S)).X) = (1 : (Grp.trivial (Over S)).X ⟶ _) :=
      toUnit_unique _ _
    exact (Category.id_comp F).symm.trans
      ((congrArg (fun a => a ≫ F) h).trans (MonObj.one_comp F))
  | succ n ih =>
    exact OrdinaryOpposite.Construction.product_trivialFrobenius p hp hS _ _ (hB 0) (ih _ (fun v => hB v.succ))

theorem groupBlockProduct_factor (n : ℕ) (K B : Fin n → Grp (Over S))
    (i : ∀ v, K v ⟶ B v)
    (hi : ∀ v (T : Grp (Over S)) (f : T ⟶ B v),
      Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS T.X = 1 →
        ∃ a : T.X ⟶ (K v).X, a ≫ (i v).hom.hom = f.hom.hom)
    (T : Grp (Over S)) (f : T ⟶ BlockProducts.Construction.groupBlockProduct n B)
    (hT : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS T.X = 1) :
    ∃ a : T.X ⟶ (BlockProducts.Construction.groupBlockProduct n K).X,
      a ≫ (BlockProducts.Construction.groupBlockProductMap n K B i).hom.hom = f.hom.hom := by
  induction n with
  | zero => exact ⟨f.hom.hom, Category.comp_id _⟩
  | succ n ih =>
    let K' := BlockProducts.Construction.groupBlockProduct n (fun v => K v.succ)
    let B' := BlockProducts.Construction.groupBlockProduct n (fun v => B v.succ)
    let j := BlockProducts.Construction.groupBlockProductMap n (fun v => K v.succ) (fun v => B v.succ) (fun v => i v.succ)
    let π₁ : B 0 ⊗ B' ⟶ B 0 := Grp.homMk (fst (B 0).X B'.X)
    let f₁ : T ⟶ B 0 := f ≫ π₁
    let f₂ : T ⟶ B' := f ≫ AnnihilatorSheaf.Construction.splitSecondProjection (B 0) B'
    obtain ⟨a, ha⟩ := hi 0 T f₁ hT
    obtain ⟨b, hb⟩ := ih _ _ _ (fun v => hi v.succ) f₂
    refine ⟨lift a b, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · change (lift a b ≫ ((i 0).hom.hom ⊗ₘ j.hom.hom)) ≫ fst (B 0).X B'.X = _
      rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
      exact ha
    · change (lift a b ≫ ((i 0).hom.hom ⊗ₘ j.hom.hom)) ≫ snd (B 0).X B'.X = _
      rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
      exact hb

end Products

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (n : ℕ) (K B : Fin n → Grp (Over (Spec (.of k)))) (i : ∀ v, K v ⟶ B v)
variable (split : Assembly.Construction.torsionGroup A p ≅ BlockProducts.Construction.groupBlockProduct n B)

/-- Detection on each block determines the actual full kernel. The
block hypotheses are instantiated by ordinary chosen/opposite geometry. -/
theorem fullBlockKernel_is_frobeniusKernel
    (hK : ∀ v, Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) (K v).X = 1)
    (hclosed : ∀ v, IsClosedImmersion (i v).hom.hom.left)
    (hlift : ∀ v (T : Grp (Over (Spec (.of k)))) (f : T ⟶ B v),
      Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) T.X = 1 →
          ∃ a : T.X ⟶ (K v).X, a ≫ (i v).hom.hom = f.hom.hom) :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
      (Assembly.Construction.fullKernelToAbelian A p n K B i split) := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
  let j := Assembly.Construction.fullKernelToAbelian A p n K B i split
  have : IsClosedImmersion j.left := Assembly.Construction.fullKernelToAbelian_closed A p n K B i hclosed split
  have : Mono j := Over.mono_of_mono_left j
  have hjF : j ≫ F = 1 := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal F _ j).mpr
    (Picard.Homomorphisms.Diagonalizable.Construction.factors_kernel_of_trivial_relativeFrobenius p (Fact.out : p.Prime) hS
      (BlockProducts.Construction.groupBlockProduct n K).X A.scheme
      (groupBlockProduct_trivialFrobenius p (Fact.out : p.Prime) hS n K hK) j)
  let N := Torsion.Construction.nativeFrobeniusKernel p k A
  let t := Torsion.Construction.nativeFrobeniusKernelToTorsion p k A
  let f : N ⟶ BlockProducts.Construction.groupBlockProduct n B := Grp.homMk (t ≫ split.hom.hom.hom)
  obtain ⟨z, hz⟩ := groupBlockProduct_factor p (Fact.out : p.Prime) hS n K B i hlift N f
    (Torsion.Construction.nativeFrobeniusKernel_frobenius p k A)
  have hzj : z ≫ j = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F := by
    let b := (BlockProducts.Construction.groupBlockProductMap n K B i).hom.hom
    have he : split.hom.hom.hom ≫ split.inv.hom.hom = 𝟙 (A.torsionScheme p) :=
      congrArg (fun a : Assembly.Construction.torsionGroup A p ⟶ Assembly.Construction.torsionGroup A p => a.hom.hom) split.hom_inv_id
    change z ≫ (b ≫ split.inv.hom.hom) ≫ A.torsionInclusion p = _
    rw [← Category.assoc z, ← Category.assoc z b, hz]
    change ((t ≫ split.hom.hom.hom) ≫ split.inv.hom.hom) ≫ A.torsionInclusion p = _
    rw [Category.assoc t, he, Category.comp_id]
    exact Torsion.Construction.nativeFrobeniusKernelToTorsion_inclusion p k A
  intro T x
  constructor
  · intro hx
    let y := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).symm ⟨x, hx⟩
    have hy : y ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F = x := congrArg Subtype.val
      ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).apply_symm_apply ⟨x, hx⟩)
    have h : (y ≫ z) ≫ j = x := (Category.assoc _ _ _).trans
      ((congrArg (fun a => y ≫ a) hzj).trans hy)
    exact ⟨y ≫ z, h, fun b hb => (cancel_mono j).mp (hb.trans h.symm)⟩
  · rintro ⟨y, hy, _⟩
    exact (congrArg (fun a => a ≫ F) hy.symm).trans
      ((Category.assoc y j F).trans ((congrArg (fun a => y ≫ a) hjF).trans (MonObj.comp_one y)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Block.Construction
