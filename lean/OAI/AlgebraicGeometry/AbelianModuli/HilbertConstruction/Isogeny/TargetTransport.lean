import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.FamilyTransport

/-! # Target Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Target isomorphisms preserve finite flat isogenies, their actual
kernel groups, and their full polarization type including finite rank. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u
variable {S : Scheme.{u}} {g h : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} {B C : Abelian.Schemes.AbelianScheme h S}

def Abelian.Schemes.AbelianScheme.Isogeny.targetTransport (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (e : B.scheme ≅ C.scheme)
    [IsMonHom e.hom] : Abelian.Schemes.AbelianScheme.Isogeny A C := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  exact { hom := p.hom ≫ e.hom
          preservesGroup := inferInstance
          finite := inferInstanceAs (IsFinite (p.hom.left ≫ e.hom.left))
          flat := inferInstanceAs (Flat (p.hom.left ≫ e.hom.left))
          surjective := inferInstanceAs (Surjective (p.hom.left ≫ e.hom.left)) }

def Abelian.Schemes.AbelianScheme.Isogeny.targetTransportKernelEquiv (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (e : B.scheme ≅ C.scheme)
    [IsMonHom e.hom] (T : Over S) : (p.targetTransport e).kernelAt T ≃* p.kernelAt T where
  toFun x := ⟨x.val, by
    change x.val ≫ p.hom = 1
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, MonObj.one_comp]
    exact MonoidHom.mem_ker.mp x.property⟩
  invFun x := ⟨x.val, by
    change x.val ≫ (p.hom ≫ e.hom) = 1
    have hx : x.val ≫ p.hom = 1 := MonoidHom.mem_ker.mp x.property
    rw [← Category.assoc, hx, MonObj.one_comp]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem Abelian.Schemes.AbelianScheme.Isogeny.targetTransport_finrank (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (e : B.scheme ≅ C.scheme)
    [IsMonHom e.hom] (c : C.scheme.left) :
    (p.targetTransport e).hom.left.finrank c = p.hom.left.finrank (e.inv.left c) := by
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  have he : e.hom.left ≫ e.inv.left = 𝟙 B.scheme.left := congrArg Over.Hom.left e.hom_inv_id
  have H : IsPullback (𝟙 A.scheme.left) (p.hom.left ≫ e.hom.left) p.hom.left e.inv.left :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.assoc, he, Category.comp_id]⟩
  exact Scheme.Hom.finrank_of_isPullback (𝟙 A.scheme.left) (p.hom.left ≫ e.hom.left)
    p.hom.left e.inv.left H c

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.targetTransport
    {A B C : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (e : B.scheme ≅ C.scheme) [IsMonHom e.hom] :
    (p.targetTransport e).HasPolarizationType δ where
  degree c := (p.targetTransport_finrank e c).trans (hp.degree (e.inv.left c))
  geometricKernel K _ _ s :=
    ⟨(p.targetTransportKernelEquiv e (Over.mk s)).trans (hp.geometricKernel K s).some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
