package convertor;

import java.io.StringWriter;
import java.util.HashSet;
import java.util.stream.Stream;

import org.semanticweb.owlapi.model.HasIRI;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNamedObject;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLProperty;
import org.semanticweb.owlapi.model.OWLPropertyExpression;
import org.semanticweb.owlapi.model.parameters.Imports;

public class Convertor {

	private int count=0;
	
	public Convertor(){
		
	}
	
	public String getComponentsID(OWLNamedObject o){
		IRI iri=o.getIRI();
		return "i"+iri.getShortForm();
	}
	
	//tricks
	public String getComponentsID(OWLIndividual o){
		if(o.isNamed()){
			IRI iri=o.asOWLNamedIndividual().getIRI();
			String result=iri.getShortForm().toLowerCase();
			//System.out.println("result:"+result);
			if(result.indexOf("#")!=-1){
				String s_iri=iri.getIRIString();
				int sharp_index=s_iri.indexOf('#');
				return "n_"+s_iri.substring(sharp_index+1);
			}else{
				return result;
			}
		}else{
			return "unnamed!";
		}
	}
	
	public void convertAxioms(OWLAxiom ax){
		Visitor v=new Visitor(this,"X",new HashSet<String>(),true);
		System.out.println(addHeader(ax.accept(v)));
	}
	
	public String addHeader(String axiom){
		StringBuffer s=new StringBuffer();
		s.append("fof(axiom"+Integer.toString(this.count)+","+"axiom,(");
		s.append(axiom);
		s.append(")");
		s.append(").");
		this.count++;
		return s.toString();
	}
	
	public void produceTPTP(OWLOntology ontology){
		Stream<OWLAxiom> abox=ontology.aboxAxioms(Imports.INCLUDED);
		System.out.println("%----------ABox-----------------");
		//abox.forEach(p->System.out.println(p));
		
		abox.forEach(p->convertAxioms(p));
//		
		System.out.println("");
		System.out.println("%----------rBox-----------------");
		Stream<OWLAxiom> rbox=ontology.rboxAxioms(Imports.INCLUDED);
		rbox.forEach(p->convertAxioms(p));
		//rbox.forEach(p->System.out.println(p));
		
		System.out.println("");
		System.out.println("%----------tBox-----------------");
		Stream<OWLAxiom> tbox=ontology.tboxAxioms(Imports.INCLUDED);
		tbox.forEach(p->convertAxioms(p));
		//tbox.forEach(p->System.out.println(p));
	}
}
