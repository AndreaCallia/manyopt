#include "OSiLWriter.h" 
#include "OSInstance.h"  
#include "OSmps2osil.h"   
#include <string>
#include <iostream>
#include <fstream>

using std::cout;   
using std::endl;
using std::string;
using std::ofstream;

int main(int argc, char* argv[])
{
  OSmps2osil *mps2osil = NULL;
  string mpsfile(argv[1]);
  ofstream osilfile;
  osilfile.open(argv[2]);
  cout << "Translating into OSiL ... " << endl;
  mps2osil = new OSmps2osil(mpsfile);
  mps2osil->createOSInstance() ;
  cout << "Translation finished." << endl;
  cout << "Saving ... ";
  OSiLWriter *w;
  w = new OSiLWriter();
  osilfile << w->writeOSiL(mps2osil->osinstance) << endl;
  osilfile.close();
  cout << "Done." << endl;
  return 0;
}
