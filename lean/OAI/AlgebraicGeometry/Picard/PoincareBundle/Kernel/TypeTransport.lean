import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Degree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Type Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport

noncomputable section

/-! Actual kernel group-scheme isomorphisms preserve the geometric elementary divisors and the full finite-flat degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

/-- A group-scheme isomorphism gives a multiplicative equivalence on every test scheme. -/
def representedPointsMulEquiv {S : Scheme.{u}} {H J : Over S} [GrpObj H] [GrpObj J]
    (e : H ≅ J) [IsMonHom e.hom] (T : Over S) : (T ⟶ H) ≃* (T ⟶ J) where
  toFun x := x ≫ e.hom
  invFun y := y ≫ e.inv
  left_inv x := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv y := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  map_mul' x y := MonObj.mul_comp x y e.hom

/-- The actual represented kernel isomorphism identifies the shared isogeny's kernel groups on every test scheme. -/
def kernelAtMulEquiv {S : Scheme.{u}} {a b c d : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S} {D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme c S} {E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B E)
    (e : Kernel.Scheme.kernelObject f.hom ≅ Kernel.Scheme.kernelObject g.hom) [IsMonHom e.hom] (T : Over S) :
    f.kernelAt T ≃* g.kernelAt T :=
  (Kernel.Scheme.kernelPointsMulEquiv f.hom T).symm.trans
    ((representedPointsMulEquiv e T).trans (Kernel.Scheme.kernelPointsMulEquiv g.hom T))

/-- Over a field, an actual isomorphism of the full kernel group schemes preserves polarization type. -/
theorem hasPolarizationType {k : Type u} [Field k] {n : ℕ}
    {A B D E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n (Spec (.of k))}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B E)
    (e : Kernel.Scheme.kernelObject f.hom ≅ Kernel.Scheme.kernelObject g.hom) [IsMonHom e.hom]
    (δ : Fin n → ℕ) (hf : f.HasPolarizationType δ) : g.HasPolarizationType δ := by
  have : ConnectedSpace D.scheme.left := GeometricallyConnected.connectedSpace_of_subsingleton D.scheme.hom
  have : ConnectedSpace E.scheme.left := GeometricallyConnected.connectedSpace_of_subsingleton E.scheme.hom
  have : IsLocallyNoetherian D.scheme.left := LocallyOfFiniteType.isLocallyNoetherian D.scheme.hom
  have : IsLocallyNoetherian E.scheme.left := LocallyOfFiniteType.isLocallyNoetherian E.scheme.hom
  have : LocallyOfFinitePresentation f.hom.left := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation g.hom.left := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let s : Spec (.of k) := ⟨⊥, inferInstance⟩
  refine ⟨?_, ?_⟩
  · intro b
    exact (Degree.degree_eq f.hom g.hom e s (η[D.scheme].left s) b).symm.trans (hf.degree _)
  · intro K _ _ t
    obtain ⟨q⟩ := hf.geometricKernel K t
    exact ⟨(kernelAtMulEquiv f g e (Over.mk t)).symm.trans q⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport
