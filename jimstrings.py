#!/usr/bin/python

g_usagestring = "" +\
								"Note: Written for Python 2.7+ OSX system standard 10.8+\n" +\
								"Usage:\n" +\
								"\n" +\
								"jimstrings.py -t LocalizableType [ -NonSenseDefaults ] [ -i InputDirectory ] [ -m MergeFile ] [ -o OutputFile ] [ -Debug ]\n" +\
								"\n" +\
								"Searches in .m, .mm, .c, .cpp, .hpp and .h files.\n" +\
								"Disgards duplicate localizations (this shouldn't be a problem) - on key only, first entry wins out.\n" +\
								"Sends output to stdout, all debugging information is sent to stderr.\n" +\
								"\n" +\
								"  e.g. jimstrings -t EErrorID -i ./iOSTemplate/Source -NonSenseDefaults -m Errors.strings > NewErrors.strings\n" +\
								"\n" +\
								"-t/--LocalizableType=LocalizableType : ErrorID, EGeneralStringID, EAccessStringID, EProgStringID or other\n" +\
								" user defined template type etc.\n" +\
								"\n" +\
								"-i/--InputDirectory='Directory' : Will default to working directory if absent. Runs all subdirs.\n" +\
								"\n" +\
								"-n/--NonSenseDefaults' : If present, the english default translation is ignored for each string,\n" +\
								" and the contents of g_nonsensedefault replaces it.\n" +\
								"\n" +\
								"-m/--MergeFile='File' : If present, merge the new strings with a previously existing strings file (enforced UTF16),\n" +\
								"  all translations in the mergefile override the english defaults from the code.\n" +\
								"\n" +\
								"-o/--OutputFile='File' : If present the strings file is written here, else it's passed to stdout. Output is UTF16.\n" +\
								"\n" +\
								"-d/--Debug' : If present, debugging information is sent to stderr.\n" +\
								"\n" +\
								"Output is a standard .strings stream in UTF16, suitable for Apple's tools.\n" +\
								"\n" +\
								"e.g. 'jimstrings -t EErrorID -NonSenseDefaults > Errors.strings'\n" +\
								"     'jimstrings -t EGeneralStringID -NonSenseDefaults -i 'iOSTemplate\Source' -o 'General.strings'\n" +\
								"     'jimstrings -t EAccessStringID -i 'iOSTemplate\Source' -m 'iOSTemplate\iOSTemplate\en_proj\Errors.strings'\n" +\
								"\n" +\
								"Expected in-file syntax of markers:\n" +\
								"\n" +\
								"  CLocalizableString< EErrorID >( EErrorID::None, \"Key\", \"English Default\", \"Comment/Description\" );\n" +\
								"  CLocalizableString< EGeneralStringID >( EGeneralStringID::State_On, \"Key\", \"English Default\", \"Comment/Description\" );\n" +\
								"  CLocalizableString< EAccessStringID >( EAccessStringID::Label_ValueIs, \"Key\", \"English Default\", \"Comment/Description\" );\n" +\
								"  CLocalizableString< EProgStringID >( EProgStringID::Time_Second_Singular, \"Key\", \"English Default\", \"Comment/Description\" );\n" +\
								"\n" +\
								"etc.\n" +\
								"\n" +\
								"Notes on Merging:\n" +\
								"  Translated strings in the merge file that do not exist in the source code anymore, will not be output.\n" +\
								"  The location of the string in the outputfile will be under the file the string was discovered in the source code,\n" +\
								"    NOT the original.\n" +\
								"  The MergeFile can be the same as the OutputFile.\n" +\
								"\n" +\
								"NOTE: 'Key' should match the enumeration name, and BOTH must be in 7bit ASCII to be in apples spec.\n" +\
								"         English Default and Command/Description are taken to be UTF8. This is enforced.\n" +\
								"\n"


###############################################################################				
#
# Modded from web code - 23rd Sep 2013
#
# Look at: https://developer.apple.com/library/ios/documentation/cocoa/Conceptual/LoadingResources/Strings/Strings.html for
#  the general format description of apple .strings resources
#
#######################################

import os, re, subprocess
import fnmatch
import sys
import getopt
import io
import codecs


#######################################
# helpers for filehash tupples

kenum = 0
kkey = 1
kdefault = 2
kcomment = 3
kfullstring = 4


#######################################

g_extensions = [ '.m', '.mm', '.c', '.cpp', '.hpp', '.h' ]
g_localizabletype = None
g_inputdirectory = '.'
g_nonsensedefault = '**TRANSLATE THIS**'
g_usenonsense = False
g_debugging = False
g_mergefile = None
g_outputfile = None


#######################################
# Prepare regex - spaces can be variable as you like
# always returns 6 groups
#  0 : The entire match
#  1 : Localizable Type [ EErrorID etc ]
#  2 : enum [ EErrorID::None etc ]
#  3 : key [ None etc ]
#  4 : default [ None etc ]
#  5 : comment/description [ No error etc ]

localizableregex = re.compile( 'CLocalizableString<\s*(\w*)\s*>\s*\(\s*(\w*::\w*)\s*,\s*"([^"]*)"\s*,\s*"([^"]*)"\s*,\s*"([^"]*)"\s*\)' )


###############################################################################				

def usage():
	sys.stderr.write( g_usagestring )


###############################################################################				
# Grabs each matching file in the tree, for all extensions

def fetch_files_recursive( directory, extensions ):
    matches = []
    for root, dirnames, filenames in os.walk( directory ):
    	for extension in extensions:
	    	for filename in fnmatch.filter( filenames, '*' + extension ):
					matches.append( os.path.join( root, filename ) )
	
#					if g_debugging == True:
#						sys.stderr.write( '    DEBUG: File "' + filename + '"\n' )

    return matches


###############################################################################				
# Parses out CLocalizedString entries from a file, removing duplicates ( based on the key )
#
# @bug Should checks that the enumeration and string keys are equal [ match 2 and 3 are the same, except for the enumbase:: in 2 ]
#
# @param pfile A file path - NOTE: We assume each file is only filtered once through us (we wipe pfilehash[ pfile ])
# @param plocalizableid 'EErrorID' etc
# @param pallowutf8 If true, allow UTF8 input, else UTF16 only
# @param pfilehash Stores a tuple per localized string, hashed on the filepath it was found in
# @param pfoundkeys A list of localized string keys found
# @param pfileforkeys One to one correspondence with the above, except it's the file the string belongs to

def parseFile( pfile, plocalizabletype, pallowutf8, pfilehash, pfoundkeys, pfileforkeys ):
	global localizableregex
	global kenum, kkey, kdefault, kcomment, kfullstring
	global g_debugging

	# Easy init of the hash
	pfilehash[ pfile ] = []

	# Open in correct unicode mode [ bomb if we can't read it ]
	if pallowutf8 == True:

		try:
			handle = io.open( pfile, 'r', encoding = 'utf-8' )
		except UnicodeDecodeError:
			try:
				handle = io.open( pfile, 'r', encoding = 'utf-16' )
			except UnicodeDecodeError:
				sys.stderr.write( 'DEBUG: Could open file "' + pfile + '" in UTF8 or UTF16 mode.\n' )
				quit( -1 )

	else:
	
		try:
			handle = io.open( pfile, 'r', encoding = 'utf-16' )
		except UnicodeDecodeError:
			sys.stderr.write( 'DEBUG: Could open file "' + pfile + '" in UTF16 mode.\n' )
			quit( -1 )
	
	content = handle.read()
			
	for result in localizableregex.finditer( content ):
		if result.group( 1 ) == plocalizabletype:

			if g_debugging == True:
				sys.stderr.write( 'DEBUG: ' + result.group( 1 ) + ', ' + result.group( 2 ) + ', ' + result.group( 3 ) + ', ' + result.group( 4 ) + ', ' + result.group( 5 ) + '\n' )
					
		#	Save the details ( in per-file hash ) and key ( in a list ), and the file for this key ( in a list )
		#  unless we've found it already, in which case, disgard and fire debug note
			if result.group( 2 ) in pfoundkeys:
				prev = pfoundkeys.index( result.group( 2 ) )
				
				if g_debugging == True:
					sys.stderr.write( '\n  DEBUG: Duplicate ID "' + result.group( 2 ) + '" in file "' + pfile + '" - previous in "' + pfileforkeys[ prev ] + '".\n\n' )
					
			else:
				pfoundkeys.append( result.group( 2 ) )
				pfileforkeys.append( pfile )
				
				# Grab the tuple - we want matches 2, 3, 4, 5, 0 stored in that order [see k*** constants]
				pfilehash[ pfile ].append( ( result.group( 2 ), result.group( 3 ), result.group( 4 ), result.group( 5 ), result.group( 0 ) ) )

	# Done
	handle.close()


###############################################################################				
# All debug notes go to stderr if g_debugging is True

def main():
	global localizableregex
	global kenum, kkey, kdefault, kcomment, kfullstring
	global g_extensions, g_localizabletype, g_inputdirectory, g_nonsensedefault, g_usenonsense, g_debugging, g_mergefile, g_outputfile
	
	
# Quick check
	if len( sys.argv ) < 2:
		usage()
		quit( -1 )


# Get Commandline options, set the options into the manager
	try:
		opts, args = getopt.getopt( sys.argv[1:], "ht:ni:m:o:d", [ "help", "LocalizableType=", "NonSenseDefaults", "InputDirectory=", "MergeFile=", "OutputFile=", "Debug" ] )
	except getopt.GetoptError, err:
		sys.stderr.write( str( err ) + '\n' )
		usage()
		sys.exit(2)
		
	for o, a in opts:
		if o in ("-h", "--help"):

			usage();
			quit();
	
		elif o in ("-t", "--LocalizableType"):
		
			g_localizabletype = a
			
		elif o in ("-n", "--NonSenseDefaults"):

			g_usenonsense = True

		elif o in ("-i", "--InputDirectory"):
		
			g_inputdirectory = a
		
		elif o in ("-m", "--MergeFile"):
		
			g_mergefile = a
			
		elif o in ("-o", "--OutputFile"):
		
			g_outputfile = a			
		
		elif o in ("-d", "--Debug"):
			
			g_debugging = True
			
		else:
			print "unhandled option", o

# Parameter checks
	if g_localizabletype == None:
		sys.stderr.write( 'LocalizableType is a required parameter.\n' )
		quit( -1 )
		
	if os.path.exists( g_inputdirectory ) <> True:
		sys.stderr.write( 'InputDirectory is required to exist: "' + g_inputdirectory + '".\n' )
		quit( -1 )
		
	if g_mergefile <> None and os.path.exists( g_mergefile ) == False:
		sys.stderr.write( 'MergeFile: "' + g_mergefile + '" doesn\'t exist.\n' )
		quit( -1 )

##############

	# DEBUG
	if g_debugging == True:

		sys.stderr.write( '\n\nDEBUG: Reading Localizable Type "' + g_localizabletype + '" from "' + g_inputdirectory + '"\n' )

		if g_usenonsense == True:
			sys.stderr.write( 'DEBUG: Using NonSense Default Translations\n' )

		if g_mergefile <> None:
			sys.stderr.write( 'DEBUG: Using MergeFile: "' + g_mergefile + '".\n' )

		if g_outputfile <> None:
			sys.stderr.write( 'DEBUG: Using OutputFile: "' + g_outputfile + '".\n' )
		else:
			sys.stderr.write( 'DEBUG: Writing output to stdout.\n' )

		sys.stderr.write( '\n' )

			
	# Grabs each localization string in the correct g_localizabletype
	filehash = {}
	foundkeys = []
	fileforkeys = []
	filelist = fetch_files_recursive( g_inputdirectory, g_extensions )
	for file in filelist:
		parseFile( file, g_localizabletype, True, filehash, foundkeys, fileforkeys )

		
	# Grab the mergefile the same way if asked (UTF16 enforced)
	if g_mergefile <> None:
	
		mergefilehash = {}
		mergefoundkeys = []
		mergefileforkeys = []
	
	
		# Parse to a separate set of structures
		parseFile( g_mergefile, g_localizabletype, False, mergefilehash, mergefoundkeys, mergefileforkeys )
	
							
		# For every string found in the source code, if it's found in the mergefile, replace its default, with the default from
		#  the mergefile. We need to keep all other parts the same, as that's where the string now resides in the inputfile
		# We also need to modify the fullstring to reflect the change.
		# ( Remember the mergefilehash has only one file, the mergefile )
		# ( Remember we don't have to merge if the defaults are the same )
		for key in foundkeys:
			if key in mergefoundkeys:
				mindex = mergefoundkeys.index( key )
				mfile = mergefileforkeys[ mindex ]
			  
				index = foundkeys.index( key )
				file = fileforkeys[ index ]
			  
				filetuple = filehash[ file ][ index ]
				mergetuple = mergefilehash[ mfile ][ mindex ]
			  
				if filetuple[ kdefault ] <> mergetuple[ kdefault ]:
			  
					newtuple = ( 	filetuple[ kenum ], \
												filetuple[ kkey ], \
												mergetuple[ kdefault ], \
												filetuple[ kcomment ], \
												'CLocalizableString<' + g_localizabletype + '>( "' + filetuple[ kenum ] + '", "' + filetuple[ kkey ] + '", "' + mergetuple[ kdefault ] + '", "' + filetuple[ kcomment ] + '" )' )
				
					filehash[ file ][ index ] = newtuple

					if g_debugging == True:
						sys.stderr.write( 'DEBUG: Merged translation of "' + filetuple[ kenum ] + '" from default "' + filetuple[ kdefault ] + '" to previous translation "' + mergetuple[ kdefault ] + '".\n' )


	# Set stdout to UTF16 mode, either to a file, or keeping stdout as normal
	# Then use print as normal - BOM is automatically written for us
	oldstdout = sys.stdout
	if g_outputfile == None:
	
		sys.stdout = codecs.getwriter( 'utf-16' )( sys.stdout )
		
		if sys.platform == "win32":
			import msvcrt
			msvcrt.setmode( sys.stdout.fileno(), os.O_BINARY )
  	  
	else:
		sys.stdout = codecs.open( g_outputfile, "w", encoding = "utf-16" )


	# output strings filewise, for files that have contents
	for file in filelist:

		strings = filehash[ file ]
		
		if len( strings ) > 0:

			print '/*'
			print '  File: "' + file + '"'
			print '*/'
			print
		
			for string in strings:
		
			# Get englishdefult, or nonsensedefault
				thedefault = string[ kdefault ]
				if g_usenonsense == True:
					thedefault = g_nonsensedefault

			# Do we have a comment?
				if string[ kcomment ] <> '':
					print '/* ' + string[ kcomment ] + ' */'		

			# Print originating statement for later merges
				print '/* ' + string[ kfullstring ] + ' */'	

			# Done
				print '"' + string[ kkey ] + '" = "' + thedefault + '";'
				print
        
	sys.stdout.close()
	sys.stdout = oldstdout

#######################################
# Cmd startup

if __name__ == "__main__":
    main()
