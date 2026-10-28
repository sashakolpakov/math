import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Transport finite flat isogenies and their polarization type through source isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g h : ℕ}
variable {A B : Abelian.Schemes.AbelianScheme g S} {C : Abelian.Schemes.AbelianScheme h S}

/-- Replace the source of an isogeny by an isomorphic abelian scheme. -/
def Abelian.Schemes.AbelianScheme.Isogeny.familyTransport (p : Abelian.Schemes.AbelianScheme.Isogeny A C) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] : Abelian.Schemes.AbelianScheme.Isogeny B C := by
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  exact
    { hom := e.inv ≫ p.hom
      preservesGroup := inferInstance
      finite := inferInstanceAs (IsFinite (e.inv.left ≫ p.hom.left))
      flat := inferInstanceAs (Flat (e.inv.left ≫ p.hom.left))
      surjective := inferInstanceAs (Surjective (e.inv.left ≫ p.hom.left)) }

/-- A source isomorphism identifies the actual kernel groups on every test scheme. -/
def Abelian.Schemes.AbelianScheme.Isogeny.familyTransportKernelEquiv (p : Abelian.Schemes.AbelianScheme.Isogeny A C) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] (T : Over S) :
    (p.familyTransport e).kernelAt T ≃* p.kernelAt T where
  toFun x := ⟨x.val ≫ e.inv, by
    change (x.val ≫ e.inv) ≫ p.hom = 1
    exact (Category.assoc _ _ _).trans (MonoidHom.mem_ker.mp x.property)⟩
  invFun x := ⟨x.val ≫ e.hom, by
    change (x.val ≫ e.hom) ≫ (e.inv ≫ p.hom) = 1
    have hx : x.val ≫ p.hom = 1 := MonoidHom.mem_ker.mp x.property
    simpa only [Category.assoc, e.hom_inv_id_assoc] using hx⟩
  left_inv x := Subtype.ext (by simp only [Category.assoc, e.inv_hom_id, Category.comp_id])
  right_inv x := Subtype.ext (by simp only [Category.assoc, e.hom_inv_id, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val e.inv)

/-- The finite-flat degree, including nonreduced length, is unchanged. -/
theorem Abelian.Schemes.AbelianScheme.Isogeny.familyTransport_finrank (p : Abelian.Schemes.AbelianScheme.Isogeny A C) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] (c : C.scheme.left) :
    (p.familyTransport e).hom.left.finrank c = p.hom.left.finrank c := by
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.inv.left p.hom.left) c

/-- Both parts of polarization type are preserved by source transport. -/
theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.familyTransport {D : Abelian.Schemes.AbelianScheme g S}
    {p : Abelian.Schemes.AbelianScheme.Isogeny A D} {δ : Fin g → ℕ} (hp : p.HasPolarizationType δ)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (p.familyTransport e).HasPolarizationType δ where
  degree d := (p.familyTransport_finrank e d).trans (hp.degree d)
  geometricKernel K _ _ s :=
    ⟨(p.familyTransportKernelEquiv e (Over.mk s)).trans (hp.geometricKernel K s).some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
