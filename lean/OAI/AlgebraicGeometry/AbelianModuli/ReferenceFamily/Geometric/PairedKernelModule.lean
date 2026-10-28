import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedKernelType
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness
import Mathlib.Algebra.Module.ZMod

/-! # Paired Kernel Module -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! A paired quotient over an algebraically closed field supplies its
own finite kernel module. The full relative module-type predicate is
proved from invariance of the actual finite kernel under field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [Field k] [IsAlgClosed k]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {b : Spec (.of k) ⟶ Spec (.of K)}
    {A B : PEL.Objects.PELObject P iota N (Over.mk b)}
    (f : Paired.PELQuotients.PairedPELQuotient A B n)

def Paired.PELQuotients.PairedPELQuotient.geometricKernelModule :=
  Additive (f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)))))

instance Paired.PELQuotients.PairedPELQuotient.geometricKernelModule_addCommGroup :
    AddCommGroup f.geometricKernelModule :=
  inferInstanceAs (AddCommGroup (Additive (f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)))))))

instance Paired.PELQuotients.PairedPELQuotient.geometricKernelModule_finite : Finite f.geometricKernelModule := by
  let : GrpObj (Picard.PoincareBundle.Kernel.Scheme.kernelObject f.forward.isogeny.hom) := Picard.PoincareBundle.Kernel.Scheme.kernelGroup f.forward.isogeny.hom
  let : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject f.forward.isogeny.hom).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f.forward.isogeny.hom
  let : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f.forward.isogeny.hom) :=
    AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness.Construction.finite_over_geometric_points (Picard.PoincareBundle.Kernel.Scheme.kernelObject f.forward.isogeny.hom) k (𝟙 (Spec (.of k)))
  let : Finite (f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k))))) :=
    Finite.of_equiv (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f.forward.isogeny.hom)
      (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv f.forward.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toEquiv
  exact inferInstanceAs (Finite (Additive (f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)))))))

instance Paired.PELQuotients.PairedPELQuotient.geometricKernelModule_zmod : Module (ZMod n) f.geometricKernelModule :=
  AddCommGroup.zmodModule (n := n) (fun x => by
    change x.toMul ^ n = 1
    apply Subtype.ext
    change x.toMul.val ^ n = 1
    have hx : x.toMul.val ≫ f.forward.isogeny.hom = 1 := x.toMul.property
    calc
      x.toMul.val ^ n = x.toMul.val ≫ (𝟙 A.polarized.abelian.scheme) ^ n := by
        rw [MonObj.comp_pow, Category.comp_id]
      _ = x.toMul.val ≫ (f.forward.isogeny.hom ≫ f.reverse.isogeny.hom) := by rw [f.forward_reverse]
      _ = 1 := by rw [← Category.assoc, hx, MonObj.one_comp])

def Paired.PELQuotients.PairedPELQuotient.geometricKernelModuleMulEquiv :
    f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃* Multiplicative f.geometricKernelModule where
  toFun x := Multiplicative.ofAdd (Additive.ofMul x)
  invFun x := x.toAdd.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem Paired.PELQuotients.PairedPELQuotient.geometricKernelModule_type :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType f.geometricKernelModule := by
  intro L _ _ c t
  exact ⟨(AbelianScheme.IsogenyQuotient.AlgebraicallyClosedKernelType.Construction.algebraicallyClosedIsogenyKernelFieldEquiv f.forward.isogeny c).symm.trans
    f.geometricKernelModuleMulEquiv⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
