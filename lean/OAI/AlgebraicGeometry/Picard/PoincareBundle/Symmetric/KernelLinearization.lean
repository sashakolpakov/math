import OAI.AlgebraicGeometry.Picard.PoincareBundle.CorrectedSubgroupTransport

/-! # Kernel Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLinearization

noncomputable section

/-! A finite kernel's symmetric regular translation defect gives an actual kernel linearization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [IsProper A.hom] [IsIntegral A.left]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd (Kernel.Scheme.kernelObject f) A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action (Kernel.Scheme.kernelInclusion f)))
  (v : ∀ T : Over (Spec (.of k)), (T ⟶ Kernel.Scheme.kernelObject f) → Γ(T.left, ⊤)ˣ)
  (hv₁ : ∀ T : Over (Spec (.of k)), v T 1 = 1)
  (hvn : ∀ {T U : Over (Spec (.of k))} (g : U ⟶ T) (a : T ⟶ Kernel.Scheme.kernelObject f),
    Units.map g.left.appTop.hom (v T a) = v U (g ≫ a))
  (hvm : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
    Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) a b * v T (a * b) =
      v T a * v T b)

/-- A regular splitting corrects the constructed translation into a genuine kernel action. -/
def linearization :
    Kernel.Linearization.KernelLinearization f (Geometric.KernelLinearization.overModulePullbacks (Spec (.of k))) L.sheaf where
  transport := fun {_T} x y a hx =>
    (CorrectedSubgroupTransport.transport (Kernel.Scheme.kernelInclusion f) L t v x y a
      ((mul_comm _ _).trans hx)).hom
  unit_compat := by
    intro T x hx
    exact congrArg Iso.hom (CorrectedSubgroupTransport.unit (Kernel.Scheme.kernelInclusion f) L t v
      x ((mul_comm _ _).trans hx) (hv₁ T))
  mul_compat := by
    intro T x y z a b c hx hy hz hc
    have hm : Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) a b * v T c =
        v T a * v T b :=
      (congrArg (fun d => Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) a b * v T d)
        hc).symm.trans (hvm T a b)
    exact congrArg Iso.hom (CorrectedSubgroupTransport.comp (Kernel.Scheme.kernelInclusion f) L t v x y z a b c
      ((mul_comm _ _).trans hx) ((mul_comm _ _).trans hy) ((mul_comm _ _).trans hz) hc hm)
  pullback_compat := by
    intro T U g x y a hx x' y' a' hx' hxx hyy ha
    exact CorrectedSubgroupTransport.natural (Kernel.Scheme.kernelInclusion f) L t v g x y a
      ((mul_comm _ _).trans hx) x' y' a' ((mul_comm _ _).trans hx') hxx hyy ha
      ((hvn g a).trans (congrArg (v U) ha))

omit v hv₁ hvn hvm in
/-- On the original finite scheme-theoretic kernel, symmetry is the sole remaining defect condition. -/
theorem exists_linearization [IsFinite f.left]
    (hs : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
      Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) a b =
        Subgroup.DefectParameters.value (Kernel.Scheme.kernelInclusion f) L (NormalizedTranslationUnit.translation (Kernel.Scheme.kernelInclusion f) L t) b a) :
    Nonempty (Kernel.Linearization.KernelLinearization f (Geometric.KernelLinearization.overModulePullbacks (Spec (.of k))) L.sheaf) := by
  have : IsFinite (Kernel.Scheme.kernelObject f).hom := Kernel.Scheme.kernel_isFinite f
  obtain ⟨v, hv₁, hvn, hvm⟩ := TranslationCocycle.exists_correction (Kernel.Scheme.kernelInclusion f) L t hs
  exact ⟨linearization f L t v hv₁ hvn hvm⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelLinearization
