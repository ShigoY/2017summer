package convertor;

import java.util.HashSet;
import java.util.stream.Stream;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;

public class ConvertorMain {
	public static void main(String[] args) throws ParseException{
		//Classes Declaration,for the purpose of extention
		Convertor convertor=null;
		OWLOntology ontology=null;
		String filename=null;
		
		//Definition Stage
		Options options=new Options();
		options.addOption("h",false,"display the help message");
		Option convert=Option.builder("c").argName("file").hasArg().desc("convert OWL to TPTP").build();
		options.addOption(convert);
		//Parsing Stage
		CommandLineParser parser=new DefaultParser();
		CommandLine cmd=parser.parse(options, args);
		HelpFormatter formatter=new HelpFormatter();
		//interrogate Stage
		if(args.length==0){
			formatter.printHelp("OWL2TPTP", options);
		}else{
			if(cmd.hasOption("c")){
				filename=cmd.getOptionValue("c");
				if(filename==null){
				
				}else{
					//System.out.println("Can be read:"+filename);
					convertor=new Convertor();
					
				}
			}else{
			
			}
		
			if(cmd.hasOption("h")){
				
				formatter.printHelp("OWL2TPTP", options);
			}
		}
		//process the ontologies and validation
		if(convertor!=null){
			OWLOntologyManager manager=OWLManager.createOWLOntologyManager();
			//args:=-c file:///D:/CL/Arbeit/ontos/pizza1.owl
			IRI fileIRI=IRI.create(filename);
			try {
				ontology=manager.loadOntology(fileIRI);
				//System.out.println(ontology.toString());
				//-----------
				
				//Abox----
				
				convertor.produceTPTP(ontology);
				
				
				
			} catch (OWLOntologyCreationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
