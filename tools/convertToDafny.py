#!/usr/bin/python


import sys, getopt


def findSize(s):
	s = s.replace(',',"")
	if('i8' in s):
		return 1
	if('i16' in s):
		return 2
	if('i24' in s):
		return 3
	if('i32' in s):
		return 4
	if('i64' in s):
		return 8
	else:
		return 8
		
def handleArg(arg,size):
	if (len(arg) <= 0):
		return
	arg = arg.replace(',',"")
	if(arg[0] == '%' or arg[0] == '@'):
		return arg
	else:
		convertedArg = "D(Int("+arg+",IntType("+str(size)+",false)))"
		return convertedArg
		
		
		
def parseLLVM(in_filename,out_filename):
	fo = open(in_filename,"r+")
	fout = open(out_filename,"w+")
	
	llvmCode = fo.readlines()
	count = 0
	insList = []
	lv = {}
	labelList = []
	totalDafnyCode = ""
	for line in llvmCode:
		print("Line{}: {}".format(count,line.strip()))
		count = count + 1
		parsedList = []
		args = line.split()
		# print (args)
		if(len(args)> 0):
			if(args[0][-1] == ':'): #this is a block name
				parsedList = []
				insList = []
				totalDafnyCode = totalDafnyCode + "var " + args[0][0:-1].replace('.',"_") + " := "
				labelList.append(args[0][0:-1].replace('.',"_"));
				# fout.write("var " + args[0][0:-1] + " := ")
				continue
			
			if(args[0][0] == '%'):
				dst = args[0]
				ins = args[2]
				# writeToOut(ins)
				parsedList.append(ins)
				parsedList.append(dst)
				
				# parsedList = handleIns(parsedList,args)
			
				if(ins == 'add' or ins == 'sub'):
					size = findSize(args[4])
					parsedList.append(str(size))
					arg1 = args[5].replace(',',"")
					arg2 = args[6].replace(',',"")
				
					arg1 = handleArg(arg1,size)
					arg2 = handleArg(arg2,size)
					parsedList.append(arg1)
					parsedList.append(arg2)
				
				if(ins == 'icmp'):
					comp = args[3]
					size = findSize(args[4])
					arg1 = args[5].replace(',',"")
					arg2 = args[6].replace(',',"")
				
					arg1 = handleArg(arg1,size)
					arg2 = handleArg(arg2,size)
					parsedList.append(comp)
					parsedList.append(str(size))
					parsedList.append(arg1)
					parsedList.append(arg2)
					
				if(ins == 'and'):
					size = findSize(args[3])
					arg1 = args[4].replace(',',"")
					arg1 = handleArg(arg1,size)
					arg2 = args[5].replace(',',"")
					arg2 = handleArg(arg2,size)
					parsedList.append(arg1)
					parsedList.append(arg2)
				
				if(ins == 'zext' or ins == 'sext'):
					size = findSize(args[3])
					arg1 = args[4].replace(',',"")
					arg1 = handleArg(arg1,size)
					parsedList.append(arg1)
					parsedList.append(str(findSize(args[6])))
				
				if(ins == 'trunc'):
					size = findSize(args[3])
					arg1 = args[4].replace(',',"")
					arg1 = handleArg(arg1,size)
					parsedList.append(str(size))
					parsedList.append(arg1)
					parsedList.append(str(findSize(args[6])))
				
				if(ins == 'lshr'):
					size = findSize(args[3])
					arg1 = args[4].replace(',',"")
					arg1 = handleArg(arg1,size)
					arg2 = args[5].replace(',',"")
					arg2 = handleArg(arg2,size)
					parsedList.append(arg1)
					parsedList.append(arg2)
			
				if(ins == 'load'):
					size = findSize(args[3])
					src = args[5].replace(',',"")
					src = handleArg(src,size)
					parsedList.append(str(size))
					parsedList.append(src)
					
				if(ins == 'alloca'):
					size = findSize(args[3])
					arg1 = args[4].replace(',',"")
					arg1 = handleArg(arg1,size)
					parsedList.append(str(size))
					# parsedList.append(arg1)
	
			
				
			if(args[0] == 'store'):
				arg1Size = findSize(args[1])
				arg1 = handleArg(args[2],arg1Size)
				parsedList.append(args[0])
				parsedList.append(arg1)
				arg2 = handleArg(args[4],arg1Size)
				parsedList.append(arg2)
				
				
			
			if(args[0] == "br"):
				if(len(args) <= 3):
					parsedList.append("UNCONDBR")
					arg1 = args[2].replace(',',"")
					parsedList.append(arg1)
				else:
					parsedList.append(args[0])
					argT = args[4].replace(',',"")
					argF = args[6].replace(',',"")
					parsedList.append(arg1)
					parsedList.append(argT)
					parsedList.append(argF)
				
			if(args[0] == 'ret'):
				parsedList.append(args[0])
				# handle void keyword
				if(args[1] == "void"):
					parsedList.append("D(Void)")
				else:
					parsedList.append(args[1])
		
				
		
			if(len(parsedList) > 0):
				formattedIns = formatIns(parsedList)
				insList.append(insToDafny(formattedIns))
				lv = handleLV(formattedIns,lv)
			
		# print (insList)
		else:
			totalDafnyCode = totalDafnyCode + createLLVMBlock(insList)
			# fout.write(createLLVMBlock(insList))
	
	# add LVS
	for lvs in lv:
		fout.write("\n" + lv[lvs])
	for i in reversed(totalDafnyCode.split("\n\n")):
		fout.write("\n\n" + i)
	fout.write("\n\n"+labelList[0])
	# Close opend file
	fo.close()
	fout.close()
	
	
def handleLV(ins,lvs):
	for i in ins:
		if("var_" in str(i) and not(i in lvs)):
			lvs[str(i)] = "var " + str(i) + " := LV(\" " + str(i) + " \");"
	return lvs
	
	
def createLLVMBlock(listOfIns):
	block = "Block(["
	for ins in listOfIns[:len(listOfIns)-1]:
		block = block + str(ins) + ",\n"
	block = block + listOfIns[len(listOfIns)-1].replace('%',"").replace('.',"_") + "]);\n\n"
	return block

def formatIns(ins):
	# print(ins)
	formattedIns = []
	for i in range(len(ins)):
		if((ins[0] == "UNCONDBR" or ins[0] == "br")):
			if(len(ins) > 3 and i==1):
				iFormat = ins[i].replace('%',"var_").replace(".","_")
			else:
				iFormat = ins[i].replace('%',"").replace(".","_")
		else:
			iFormat = ins[i].replace('%',"var_").replace('@',"var_").replace(".","_")
		formattedIns.append(iFormat)
	return formattedIns
		
def insToDafny(ins):
	insStart = "Ins("
	insStart = insStart+ins[0].upper()+"("
	for item in ins[1:len(ins)-1]:
		# itemStripped = item.replace('%',"var_")
# 		itemStripped = itemStripped.replace(".","_")
		insStart = insStart + item + ","
	insStart = insStart + ins[len(ins)-1] + "))"
	return insStart
	
	
def main(argv):
   inputfile = ''
   outputfile = ''
   try:
      opts, args = getopt.getopt(argv,"hi:o:",["ifile=","ofile="])
   except getopt.GetoptError:
      print('test.py -i <inputfile> -o <outputfile>')
      sys.exit(2)
   for opt, arg in opts:
      if opt == '-h':
         print('test.py -i <inputfile> -o <outputfile>')
         sys.exit()
      elif opt in ("-i", "--ifile"):
         inputfile = arg
      elif opt in ("-o", "--ofile"):
         outputfile = arg
   print('Input file is "', inputfile)
   print('Output file is "', outputfile)
   # cleanInputFile(inputfile)
   parseLLVM(inputfile,outputfile)
   
   #sanitze keyword 'return'
   with open(outputfile) as f:
	   newText=f.read().replace('return', 'return_')

   with open(outputfile, "w") as f:
	   f.write(newText)

if __name__ == "__main__":
   main(sys.argv[1:])
	 
	 
print("DONE")

#######


	
	
	
	
	
	
	