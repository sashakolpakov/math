import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CanonicalPEL
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELMapReflection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldAutomorphismDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange

/-! # PEL Automorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! Full PEL automorphisms descend over algebraically closed field
extensions. Their dual, Poincare, polarization, action, and full marking
are recovered from the actual abelian map, without extra descent inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g N : ℕ}

section Reflection
variable {k : Type} [Field k] [IsAlgClosed k]
  {P : PEL.PELFamilyData R g N (Spec (.of k))}

def PELModuli.PELFamilyIso.ofPullbackAutomorphism {T : Scheme} (b : T ⟶ Spec (.of k))
    [(Over.pullback b).Faithful]
    (d : P.abelian.scheme ≅ P.abelian.scheme) [IsMonHom d.hom]
    (e : PELModuli.PELFamilyIso (P.pullback b) (P.pullback b))
    (hd : (Over.pullback b).map d.hom = e.abelian.hom) : PELModuli.PELFamilyIso P P := by
  apply PELModuli.PELFamilyIso.ofAbelianIso d
  · have hp := PELMapReflection.pel_native_polarization_of_pullback b d.hom e.toIsogeny hd
    simp only [pow_one] at hp
    exact hp
  · intro r
    exact PELMapReflection.pel_action_of_pullback b d.hom e.toIsogeny hd r
  · apply LevelBaseChange.preservesFullLevel_of_pullback P.abelian P.marking d.hom b
    have hl : AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel (P.marking.pullback b) e.abelian.hom := e.marking
    exact hd.symm ▸ hl

end Reflection

variable (k B : Type) [Field k] [IsAlgClosed k] [Field B] [Algebra k B]
  (P : PEL.PELFamilyData R g N (Spec (.of k)))

theorem PELModuli.PELFamilyIso.field_pel_automorphism_descends
    (e : PELModuli.PELFamilyIso (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B))))
      (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B))))) :
    ∃ d : PELModuli.PELFamilyIso P P,
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).map d.abelian.hom =
        e.abelian.hom := by
  obtain ⟨d, hd, he⟩ := FieldAutomorphismDescent.field_group_automorphism_descends k B P.abelian e.abelian
  have : IsMonHom d.hom := hd
  have : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Faithful :=
    FieldAutomorphismDescent.fieldBaseChange_faithful k B
  exact ⟨PELModuli.PELFamilyIso.ofPullbackAutomorphism (Spec.map (CommRingCat.ofHom (algebraMap k B))) d e he, he⟩

end

/-! PEL automorphism rigidity transfers between field extensions of an
algebraically closed field of definition. All maps are descended and
compared as actual scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

section Fields
variable {k B : Type} [Field k] [Field B]

theorem PELAutomorphismDescent.fieldPullback_faithful (b : Spec (.of B) ⟶ Spec (.of k)) :
    (Over.pullback b).Faithful := by
  have : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  infer_instance

end Fields

section IsoTransport
variable {R : Type} [CommRing R] {S : Scheme} {g N : ℕ}
  {P Q : PEL.PELFamilyData R g N S}

theorem PELModuli.PELFamilyIso.abelian_eq_id_via (e : PELModuli.PELFamilyIso P P) (a : PELModuli.PELFamilyIso P Q)
    (hr : ∀ j : PELModuli.PELFamilyIso Q Q, j.abelian.hom = 𝟙 Q.abelian.scheme) :
    e.abelian.hom = 𝟙 P.abelian.scheme := by
  have hj := hr (a.symm.trans (e.trans a))
  change a.abelian.inv ≫ (e.abelian.hom ≫ a.abelian.hom) = 𝟙 Q.abelian.scheme at hj
  have hh := congrArg (fun z => a.abelian.hom ≫ z ≫ a.abelian.inv) hj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using hh

end IsoTransport

variable {R k B C : Type} [CommRing R] [Field k] [IsAlgClosed k] [Field B] [Field C]
  {g N : ℕ} (P : PEL.PELFamilyData R g N (Spec (.of k)))

theorem PELModuli.PELFamilyIso.field_pel_automorphism_descends_spec (b : Spec (.of B) ⟶ Spec (.of k))
    (e : PELModuli.PELFamilyIso (P.pullback b) (P.pullback b)) :
    ∃ d : PELModuli.PELFamilyIso P P, (Over.pullback b).map d.abelian.hom = e.abelian.hom := by
  obtain ⟨r, rfl⟩ := Spec.map_surjective b
  let : Algebra k B := r.hom.toAlgebra
  exact PELModuli.PELFamilyIso.field_pel_automorphism_descends k B P e

theorem PELModuli.PELFamilyIso.abelian_eq_id_of_rigid_extension (b : Spec (.of B) ⟶ Spec (.of k))
    (c : Spec (.of C) ⟶ Spec (.of k))
    (hr : ∀ j : PELModuli.PELFamilyIso (P.pullback c) (P.pullback c),
      j.abelian.hom = 𝟙 (P.pullback c).abelian.scheme)
    (e : PELModuli.PELFamilyIso (P.pullback b) (P.pullback b)) :
    e.abelian.hom = 𝟙 (P.pullback b).abelian.scheme := by
  obtain ⟨d, hd⟩ := PELModuli.PELFamilyIso.field_pel_automorphism_descends_spec P b e
  have : (Over.pullback c).Faithful := PELAutomorphismDescent.fieldPullback_faithful c
  have hc : (Over.pullback c).map d.abelian.hom = 𝟙 (P.pullback c).abelian.scheme :=
    hr (d.pullback c)
  have hi : d.abelian.hom = 𝟙 P.abelian.scheme :=
    (Over.pullback c).map_injective (hc.trans ((Over.pullback c).map_id P.abelian.scheme).symm)
  exact hd.symm.trans ((congrArg (Over.pullback b).map hi).trans
    ((Over.pullback b).map_id P.abelian.scheme))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
