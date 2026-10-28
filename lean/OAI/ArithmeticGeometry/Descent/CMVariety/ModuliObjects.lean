import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Functor

/-! # Moduli Objects -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian

noncomputable section

/-!
The concrete moduli problem used for CMAbelianVariety: polarized abelian schemes with
full level and finitely many specified algebraic endomorphisms. Relations
or PEL signature conditions can be imposed by an arithmetic subfunctor.
All objects, isomorphisms, and base changes are actual scheme data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Polarized full-level abelian data with a finite tuple of endomorphisms. -/
structure EnhancedAbelianData (g : ℕ) (δ : Fin g → ℕ) (N r : ℕ) (S : Scheme.{u}) where
  polarized : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S
  endomorphism : Fin r → (polarized.abelian.scheme ⟶ polarized.abelian.scheme)
  endomorphism_group : ∀ i, IsMonHom (endomorphism i)

attribute [instance] EnhancedAbelianData.endomorphism_group

variable {g N r : ℕ} {δ : Fin g → ℕ} {S T V : Scheme.{u}}

/-- Isomorphisms preserve the polarization, level, and every designated
algebraic endomorphism. -/
structure EnhancedAbelianIso (A B : EnhancedAbelianData g δ N r S) where
  polarized : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.polarized B.polarized
  equivariant : ∀ i, A.endomorphism i ≫ polarized.abelian.hom =
    polarized.abelian.hom ≫ B.endomorphism i

namespace EnhancedAbelianIso

def refl (A : EnhancedAbelianData g δ N r S) : EnhancedAbelianIso A A where
  polarized := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl A.polarized
  equivariant i := by simp [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl]

def symm {A B : EnhancedAbelianData g δ N r S}
    (e : EnhancedAbelianIso A B) : EnhancedAbelianIso B A where
  polarized := e.polarized.symm
  equivariant i := by
    change B.endomorphism i ≫ e.polarized.abelian.inv =
      e.polarized.abelian.inv ≫ A.endomorphism i
    apply (cancel_epi e.polarized.abelian.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← e.equivariant]
    simp

def trans {A B C : EnhancedAbelianData g δ N r S}
    (e : EnhancedAbelianIso A B) (f : EnhancedAbelianIso B C) :
    EnhancedAbelianIso A C where
  polarized := e.polarized.trans f.polarized
  equivariant i := by
    change A.endomorphism i ≫ (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) =
      (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) ≫ C.endomorphism i
    rw [← Category.assoc, e.equivariant, Category.assoc, f.equivariant, ← Category.assoc]

end EnhancedAbelianIso

def EnhancedAbelianData.pullback (A : EnhancedAbelianData g δ N r S) (f : T ⟶ S) :
    EnhancedAbelianData g δ N r T where
  polarized := A.polarized.pullback f
  endomorphism i := (Over.pullback f).map (A.endomorphism i)
  endomorphism_group i := by
    let : GrpObj ((Over.pullback f).obj A.polarized.abelian.scheme) := Functor.grpObjObj
    exact inferInstanceAs (IsMonHom ((Over.pullback f).map (A.endomorphism i)))

def EnhancedAbelianIso.pullback {A B : EnhancedAbelianData g δ N r S}
    (e : EnhancedAbelianIso A B) (f : T ⟶ S) :
    EnhancedAbelianIso (A.pullback f) (B.pullback f) where
  polarized := e.polarized.pullback f
  equivariant i := by
    change (Over.pullback f).map (A.endomorphism i) ≫
      (Over.pullback f).map e.polarized.abelian.hom =
        (Over.pullback f).map e.polarized.abelian.hom ≫
          (Over.pullback f).map (B.endomorphism i)
    rw [← Functor.map_comp, e.equivariant, Functor.map_comp]

def EnhancedAbelianIso.pullbackId (A : EnhancedAbelianData g δ N r S) :
    EnhancedAbelianIso (A.pullback (𝟙 S)) A where
  polarized := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized
  equivariant i := by
    change (Over.pullback (𝟙 S)).map (A.endomorphism i) ≫
      A.polarized.abelian.pullbackIdIso.hom =
        A.polarized.abelian.pullbackIdIso.hom ≫ A.endomorphism i
    rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (A.endomorphism i)

def EnhancedAbelianIso.pullbackComp (A : EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : V ⟶ T) :
    EnhancedAbelianIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  polarized := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.polarized f h
  equivariant i := by
    change (Over.pullback h).map ((Over.pullback f).map (A.endomorphism i)) ≫
      (A.polarized.abelian.pullbackCompIso f h).inv =
        (A.polarized.abelian.pullbackCompIso f h).inv ≫
          (Over.pullback (h ≫ f)).map (A.endomorphism i)
    rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h f).inv.naturality (A.endomorphism i)

def enhancedAbelianSetoid (g : ℕ) (δ : Fin g → ℕ) (N r : ℕ) (S : Scheme.{u}) :
    Setoid (EnhancedAbelianData g δ N r S) where
  r A B := Nonempty (EnhancedAbelianIso A B)
  iseqv := {
    refl A := ⟨EnhancedAbelianIso.refl A⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

def EnhancedAbelianClasses (g : ℕ) (δ : Fin g → ℕ) (N r : ℕ) (S : Scheme.{u}) :=
  Quotient (enhancedAbelianSetoid g δ N r S)

def EnhancedAbelianData.classOf (A : EnhancedAbelianData g δ N r S) :
    EnhancedAbelianClasses g δ N r S := Quotient.mk _ A

theorem EnhancedAbelianData.classOf_eq_iff (A B : EnhancedAbelianData g δ N r S) :
    A.classOf = B.classOf ↔ Nonempty (EnhancedAbelianIso A B) := Quotient.eq

def EnhancedAbelianClasses.pullback (f : T ⟶ S) :
    EnhancedAbelianClasses g δ N r S → EnhancedAbelianClasses g δ N r T :=
  Quotient.map (fun A => A.pullback f) (fun _ _ ⟨e⟩ => ⟨e.pullback f⟩)

theorem EnhancedAbelianClasses.pullback_id (q : EnhancedAbelianClasses g δ N r S) :
    EnhancedAbelianClasses.pullback (𝟙 S) q = q := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨EnhancedAbelianIso.pullbackId A⟩

theorem EnhancedAbelianClasses.pullback_comp (f : T ⟶ S) (h : V ⟶ T)
    (q : EnhancedAbelianClasses g δ N r S) :
    EnhancedAbelianClasses.pullback (h ≫ f) q = EnhancedAbelianClasses.pullback h (EnhancedAbelianClasses.pullback f q) := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(EnhancedAbelianIso.pullbackComp A f h).symm⟩

/-- The presheaf of concrete enhanced abelian moduli classes. -/
def enhancedAbelianModuli (g : ℕ) (δ : Fin g → ℕ) (N r : ℕ) :
    Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := EnhancedAbelianClasses g δ N r S.unop
  map f := TypeCat.ofHom (EnhancedAbelianClasses.pullback f.unop)
  map_id _ := by ext q; exact EnhancedAbelianClasses.pullback_id q
  map_comp f h := by ext q; exact EnhancedAbelianClasses.pullback_comp f.unop h.unop q

def enhancedAbelianModuliOver (g : ℕ) (δ : Fin g → ℕ) (N r : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Over.forget S).op ⋙ enhancedAbelianModuli g δ N r

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian
