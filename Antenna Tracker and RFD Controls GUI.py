#################################################################################################################################
#	   Antenna Tracker Controller for Trident Antenna Array and RFD Radio Controller											#
#																																#
#	   Author:	Austin Langford, AEM																							#
#	   Based on work from Scott Miller, CpE, Dylan Trafford, CpE, and David Schwerr of the Montana Space Grant Consortium		#
#	   Software created for use by the Minnesota Space Grant Consortium								   							#
#	   Purpose: To acquire the location of a balloon in flight, and aim the array of antennae at the balloon					#
#	   Additional Features: RFD 900 based Command Center and Image Reception									 				#
#	   Creation Date: March 2016																								#
#	   Last Edit Date: August 19, 2016																							#
#################################################################################################################################

from ui_trackermain import Ui_MainWindow
import PyQt4
from PyQt4 import QtCore, QtGui
from PyQt4.QtWebKit import *
from PyQt4.QtCore import *
from PyQt4.QtGui import QApplication, QMainWindow, QTextEdit, QPushButton, QMessageBox, QLabel, QPixmap
from PyQt4.QtGui import *
import geomag
import sys
import os
import math
import serial
import time
import MySQLdb					  # database section, help from: http://www.tutorialspoint.com/python/python_database_access.htm
import numpy as np
from datetime import *
import time
import matplotlib
import base64					   # = encodes an image in b64 Strings (and decodes)
import hashlib					  # = generates hashes
import serial.tools.list_ports
import threading

from matplotlib.figure import Figure
from matplotlib.backends.backend_qt4agg import FigureCanvasQTAgg as FigureCanvas

matplotlib.use('Qt4Agg')
matplotlib.rcParams['backend.qt4']='PyQt4'

##########################
#### GLOBAL VARIABLES ####
##########################

# Ground station location
groundLat = 0.00
groundLon = 0.00
groundAlt = 0.00
centerBear = 0.00
antennaBear = 0.00
antennaEle = 0.00
moveIncrement = 2.0

# Booleans for Ground Station and Tracking Method settings
settingsUpdated = False
servoAttached = False
rfdAttached = False
arduinoAttached = False
aprsAttached = False
useIridium = False
useRFD = False
useAPRS = False
autotrackOnline = False
getLocal = False
manualLocal = False
centerBearSet = False
aprsStarted = False
iridiumStarted = False
iridiumInterrupt = False
aprsInterrupt = False
autotrackBlock = False
calibrationReady = False
inSliderMode = False

# use these to manually tweak the tracking (ie if its still off a little after aligning)
panOffset = 0		  # increase to turn right, decrease to turn left
tiltOffset = 0		  # increase to raise, decrease to lower
previousPan = 127	   #Memory for last position (To account for backlash)

# Pololu servo controller commands using Mini SSC Protocol, 
#  see: http://www.pololu.com/docs/0J40/5.c  
# Shouldn't need to change these usually
moveCommand = 0xFF
accelCommand = 0x89			 
speedCommand = 0x87

# Shouldn't need to change these unless you change to some exotic servos
servo_min = 0
servo_max = 254

# change the movement speed etc of ubiquity tilt servo
tiltChannel = 0
tiltRange = 360
tiltAccel = 1
tiltSpeed = 1
tilt_angle_min = -180		#-90
tilt_angle_max = 180		 #90

# change the movement speed etc of ubiquity pan servo
panChannel = 1
panRange = 360
panAccel = 1
panSpeed = 3

#RFD Commands Controls
rfdCommandsOnline = False
commandInterrupt = False
listenInterrupt = False
rfdListenOnline = False

payloadList = []		# List of payloads in this flight
currentBalloon = None
mapMade = False
googleMapsApiKey = ''		# https://developers.google.com/maps/documentation/javascript/get-api-key

# Save Data Boolean
saveData = False

#SQL Access
db_host = "153.90.202.51"
db_user = "scott"
db_passwd = "Jewe1947"
db_name = "freemanproject"			

class WebView(PyQt4.QtWebKit.QWebView):
	""" A class that allows messages from JavaScript being run in a QWebView to be printed """
	def javaScriptConsoleMessage(self, message, line, source):
		if source:
			print('line(%s) source(%s): %s' % (line, source, message))
		else:
			print(message)

class BalloonUpdate(object):
	"""
	A class to hold all of the information in a new balloon position and pointing update
	"""

	def __init__(self,time,seconds,lat,lon,alt,trackingMethod):
		global saveData, groundLat, groundLon, groundAlt
		self.time = time
		self.seconds = seconds
		self.lat = lat
		self.lon = lon
		self.alt = alt
		self.trackingMethod = trackingMethod

		### Calculate pointing values and distances ###
		distanceToTarget = haversine(groundLat, groundLon, self.lat, self.lon)
		self.bear = bearing(groundLat, groundLon, self.lat, self.lon)
		self.ele = elevationAngle(self.alt,groundAlt,distanceToTarget)
		self.los = losDistance(self.alt,groundAlt,distanceToTarget)
		self.magDec = geomag.declination(dlat = self.lat,dlon = self.lon, h = self.alt)

	def getTime(self):
		return self.time

	def getLat(self):
		return self.lat

	def getLon(self):
		return self.lon

	def getAlt(self):
		return self.alt

	def getBear(self):
		return self.bear

	def getEle(self):
		return self.ele

	def getLOS(self):
		return self.los

	def getMagDec(self):
		return self.magDec

	def getTrackingMethod(self):
		return self.trackingMethod
		
	def getSeconds(self):
		return self.seconds

class Payload:
	""" 
	A class to associate a payload's name with its messages and GPS updates, 
	as well as with its associated browsers in the main GUI
	"""
	
	def __init__(self, name,messageBrowser,gpsBrowser):
		self.name = name
		self.gpsUpdates = []
		self.messages = []
		self.newMessages = []
		self.newGPSUpdates = []
		self.messageBrowser = messageBrowser
		self.gpsBrowser = gpsBrowser
		self.map = False
		self.newLocation = False
		self.lat = 0.00
		self.lon = 0.00
		self.alt = 0.00

	def getName(self):		# Returns the payload name
		return self.name

	def addMessage(self,msg):			# Determines if a message is actually a GPS update, sorts it appropriately
		temp = PayloadMessage(msg)
		if len(temp.getMessage().split(',')) == 5:		# GPS Updates are always comma separated with a length of 5
			self.gpsUpdates.append(temp)
			self.newGPSUpdates.append(temp)
			self.time = temp.getMessage().split(',')[0]
			self.lat = temp.getMessage().split(',')[1]
			self.lon = temp.getMessage().split(',')[2]
			self.alt = temp.getMessage().split(',')[3]
			self.sat = temp.getMessage().split(',')[4]
			self.newLocation = True
		else:
			self.messages.append(temp)
			self.newMessages.append(temp)
		return 1

	def addWebview(self, webview):
		self.webview = webview
		self.map = True
		
	def updateMap(self):
		self.webview.setHtml(getMapHtml(self.lat,self.lon))
		self.newLocation = False
		
	def hasMap(self):
		return self.map
		
	def inNewLocation(self):
		return self.newLocation
		
	def getGPSUpdates(self):			# Returns the list of GPS Updates
		return self.gpsUpdates

	def getMessages(self):				# Returns the list of Messages
		return self.messages

	def getNewMessages(self):			# Returns a list of messages received since the last time this function was called
		temp = self.newMessages
		self.newMessages = []
		return temp
		
	def getNewGPSUpdates(self):			# Returns a list of GPS updates received since the last time this function was called
		temp = self.newGPSUpdates
		self.newGPSUpdates = []
		return temp
		
	def getMessageBrowser(self):		# Returns the message text browser associated with this payload
		return self.messageBrowser
		
	def getGPSBrowser(self):			# Returns the GPS text browser associated with this payload
		return self.gpsBrowser

class PayloadMessage:
	"""
	A class to manage message received from payloads in flight.
	Holds the text of the message, as well as a timestamp for
	when the message was received.
	"""
	
	def __init__(self,msg):			# Create the timestamp and message when this object is created
		self.message = msg
		self.timestamp = datetime.today().strftime('%H:%M:%S')

	def getMessage(self):			# Returns the message
		return self.message

	def getTimestamp(self):			# Returns the timestamp
		return self.timestamp

class SerialDevice:
	""" A class to manage serial devices """

	def __init__(self,port,baud,timeout):
		self.port = port
		self.baud = baud
		self.timeout = timeout

	def getPort(self):
		return self.port

	def getBaud(self):
		return self.baud

	def getTimeout(self):
		return self.timeout

	def getDevice(self):
		return serial.Serial(port = self.port, baudrate = self.baud, timeout = self.timeout)


class Unbuffered:
	""" A class to eliminate the serial buffer """
	def __init__(self,stream):
		self.stream = stream
	def write(self,data):
		self.stream.write(data)
		self.stream.flush()
	def flush(self):
		self.stream.flush()
	def close(self):
		self.stream.close()

class Worker (QtCore.QObject):
	""" A class to hold a function that will be run in a separate thread """
	start = pyqtSignal(str)
	finished = pyqtSignal()
	
	def __init__(self, function, *args, **kwargs):
		super(Worker, self).__init__()
		self.function = function
		self.args = args
		self.kwargs = kwargs
		
	def run(self):			# When run, runs the function
		self.function(*self.args, **self.kwargs)
		
class RfdThread(QtCore.QThread):
	""" 
	A class that inherits QThread. Has the signals needed to update the
	various GUI objects that need to be updated from this side thread
	"""
	
	newCommandText = pyqtSignal(str)
	newStillText = pyqtSignal(str)
	payloadUpdate = pyqtSignal(str)
	newProgress = pyqtSignal(int,int)
	newPicture = pyqtSignal(str)
	newLocation = pyqtSignal(BalloonUpdate)
	requestConfirmation = pyqtSignal(str)
	newPicSliderValues = pyqtSignal()
	
	def __init__(self, parent=None):
		super(RfdThread, self).__init__(parent)

class DataThread(QtCore.QThread):
	"""
	A class that inherits QThread. Has signals needed to update the balloon location
	"""

	newLocation = pyqtSignal(BalloonUpdate)

	def __init__(self,parent=None):
		super(DataThread, self).__init__(parent)
			
class MainWindow(QMainWindow,Ui_MainWindow):
	""" The Main GUI Window """
	def __init__(self, parent=None):
		global currentBalloon
		super(MainWindow, self).__init__(parent)
		self.setupUi(self)							# Uses the GUI built in QtCreator and interpreted using pyuic to add all of the widgets to the window
		
		### Worker Thread Setup ###
		self.threadPool = []				# To hold the threads to be double sure they never get garbage collected and eliminated
		self.rfdThread = RfdThread()
		self.rfdThread.daemon = True 		# If you make a side thread's daemon True, it dies when the main GUI is killed
		self.iridiumThread = DataThread()
		self.iridiumThread.daemon = True
		self.aprsThread = DataThread()
		self.aprsThread.daemon = True

		# Signal Connections from Side Threads
		self.rfdThread.newCommandText.connect(self.updateRFDCommandsText)
		self.rfdThread.newStillText.connect(self.updateStillImageSystemText)
		self.rfdThread.payloadUpdate.connect(self.updatePayloads)
		self.rfdThread.newPicture.connect(self.updatePicture)
		self.rfdThread.newProgress.connect(self.updatePictureProgress)
		self.rfdThread.newLocation.connect(self.updateBalloonLocation)
		self.rfdThread.requestConfirmation.connect(self.highResConfirmationCheck)
		self.rfdThread.newPicSliderValues.connect(self.updateStillImageValues)
		self.iridiumThread.newLocation.connect(self.updateBalloonLocation)
		self.aprsThread.newLocation.connect(self.updateBalloonLocation)

		# Start the threads, they should run forever, and add them to the thread pool
		self.rfdThread.start()
		self.iridiumThread.start()
		self.aprsThread.start()
		self.threadPool.append(self.rfdThread)
		self.threadPool.append(self.iridiumThread)
		self.threadPool.append(self.aprsThread)
		
		### Button Function Link Setup ###
		self.updateSettings.clicked.connect(self.getSettings)
		self.antennaCenter.clicked.connect(self.moveToCenterPos)
		self.pointAtBalloon.clicked.connect(self.pointToMostRecentBalloon)
		self.trackerLaunch.clicked.connect(self.setAutotrack)
		self.recalibrateCenterBearing.clicked.connect(self.calibrateIMU)
		self.checkComPorts.clicked.connect(self.searchComPorts)

		# Manual Entry Button Links
		self.ManualEntryUpdateButton.clicked.connect(self.manualEntryUpdate)
		self.ManualAngleEntryButton.clicked.connect(self.manualAngleEntryUpdate)
		self.sliderButton.clicked.connect(lambda: self.sliderControl("click"))				# lambda allows for passing an additional argument so one function can handle all the buttons
		self.panServoSlider.valueChanged.connect(lambda: self.sliderControl("slide"))
		self.tiltServoSlider.valueChanged.connect(lambda: self.sliderControl("slide"))

		# Trim Button Links
		self.trimUpButton.clicked.connect(lambda: self.trimControl('up'))
		self.trimDownButton.clicked.connect(lambda: self.trimControl('down'))
		self.trimLeftButton.clicked.connect(lambda: self.trimControl('left'))
		self.trimRightButton.clicked.connect(lambda: self.trimControl('right'))
		self.trimResetButton.clicked.connect(lambda: self.trimControl('reset'))

		# RFD Control Links
		self.rfdCommandButton.clicked.connect(self.rfdCommandsButtonPress)
		self.rfdListenButton.clicked.connect(self.rfdListenButtonPress)
		self.getPiRuntimeDataButton.clicked.connect(self.getPiRuntimeDataButtonPress)

		# Still Image Control Links
		self.stillImageOnlineButton.clicked.connect(self.toggleStillImageSystem)
		self.mostRecentImageButton.clicked.connect(lambda: self.stillImageButtonPress('mostRecent'))
		self.imageDataTxtButton.clicked.connect(lambda: self.stillImageButtonPress('selectImage'))
		self.picDefaultSettingsButton.clicked.connect(self.picDefaultSettings)
		self.picSendNewSettingsButton.clicked.connect(lambda: self.stillImageButtonPress('sendNewSettings'))
		self.picGetSettingsButton.clicked.connect(lambda: self.stillImageButtonPress('getPicSettings'))
		self.connectionTestButton.clicked.connect(lambda: self.stillImageButtonPress('timeSync'))
		self.picHorizontalFlipButton.clicked.connect(lambda: self.stillImageButtonPress('HFlip'))
		self.picVerticalFlipButton.clicked.connect(lambda: self.stillImageButtonPress('VFlip'))

		# Make sure the allowed combination of auto tracking checkboxes are enabled
		self.autoDisabled.stateChanged.connect(self.disabledChecked)
		self.autoIridium.stateChanged.connect(self.autotrackChecked)
		self.autoAPRS.stateChanged.connect(self.autotrackChecked)
		self.autoRFD.stateChanged.connect(self.autotrackChecked)

		# Still Image System Variables
		self.stillImageOnline = False
		self.wordlength = 7000		  									# Variable to determine spacing of checksum. Ex. wordlength = 1000 will send one thousand bits before calculating and verifying checksum
		self.extension = ".jpg"
		self.displayPhotoPath = "Images/MnSGC_Logo_highRes.png"			# The starting display photo is the logo of the MnSGC

		# Picture Qualities
		self.picWidth = 650
		self.picHeight = 450
		self.picSharpness = 0
		self.picBrightness = 50
		self.picContrast = 0
		self.picSaturation = 0
		self.picISO = 400
	
		### Inital Still Image System Picture Display Setup ###
		self.tabs.resizeEvent = self.resizePicture
		self.picLabel.setScaledContents(True)
		pm = QPixmap(self.displayPhotoPath)		# Create a pixmap from the default image
		scaledPm = pm.scaled(self.picLabel.size(),QtCore.Qt.KeepAspectRatio,QtCore.Qt.SmoothTransformation)		# Scale the pixmap
		self.picLabel.setPixmap(scaledPm)			# Set the label to the map
		self.picLabel.show()				# Show the image
		
		### Still Image Slider Updates ###
		self.picWidthSlider.valueChanged.connect(self.updatePicSliderValues)			# These make sure the number next to the slider represents the slider value
		self.picHeightSlider.valueChanged.connect(self.updatePicSliderValues)
		self.picSharpSlider.valueChanged.connect(self.updatePicSliderValues)
		self.picBrightSlider.valueChanged.connect(self.updatePicSliderValues)
		self.picContrastSlider.valueChanged.connect(self.updatePicSliderValues)
		self.picSaturationSlider.valueChanged.connect(self.updatePicSliderValues)
		self.picISOSlider.valueChanged.connect(self.updatePicSliderValues)
		
		### Graph Setup ###
		self.figure = Figure()
		self.canvas = FigureCanvas(self.figure)
		layout = QtGui.QVBoxLayout()
		layout.addWidget(self.canvas)
		self.graphWidget.setLayout(layout)

		# Tracking Labels for APRS and Iridium
		self.callsign = ""		# For the EAGLE Flight Computer
		self.IMEI = ""			# For the Iridium Modem

		#Graphing Arrays
		self.receivedTime = np.array([])
		self.receivedLat = np.array([])
		self.receivedLon = np.array([])
		self.receivedAlt = np.array([])
		self.losLog = np.array([])
		self.elevationLog = np.array([])
		self.bearingLog = np.array([])

		### Determine Serial Connections ###
		self.searchComPorts()
		
		currentBalloon = BalloonUpdate('',0,0,0,0,'')
		self.tabs.setCurrentIndex(0)
		
	def setAutotrack(self):
		""" Toggles autotracking """
		global autotrackOnline, currentBalloon
		if autotrackOnline:
			autotrackOnline = False
			#Update a nice and pretty status indicator in red
			self.status.setText("Offline")
			self.changeTextColor(self.status,"red")
			self.trackerLaunch.setText("Launch Antenna Tracker")
			
		else:
			autotrackOnline = True
			self.tabs.setCurrentIndex(1)
			self.antennaOnline(currentBalloon)

	def updateBalloonLocation(self,update):
		""" Updates the tracker with the latest balloon location """
		global currentBalloon
		if(update.getSeconds() < currentBalloon.getSeconds()):
			return
		self.antennaOnline(update)
		self.refresh(update)
		currentBalloon = update
		if(internetAccess and mapMade):
			self.mapView.setHtml(getMapHtml(update.getLat(),update.getLon()))
	
	def updateIncoming(self,row,column,value):
		""" Update the Incoming GPS Data grid with the newest values """
		self.incomingDataTable.setItem(column,row,QtGui.QTableWidgetItem(str(value)))
		
	def updateGround(self,row,column,value):
		""" Update the Ground Station Data grid with the newest values """
		self.groundDataTable.setItem(column,row,QtGui.QTableWidgetItem(str(value)))
		
	def refresh(self,update):
		""" Refreshs the info grids and plots with the newest values """
		### Update the info grid with the newest balloon information ###
		self.updateIncoming(0,0,update.getTime())
		self.updateIncoming(0,1,update.getLat())
		self.updateIncoming(0,2,update.getLon())
		self.updateIncoming(0,3,round(update.getAlt(),2))
		self.updateIncoming(0,4,round(update.getEle(),2))
		self.updateIncoming(0,5,round(update.getBear(),2))
		self.updateIncoming(0,6,round(update.getLOS(),2))
		self.updateIncoming(0,7,round(update.getMagDec(),2))
		self.updateIncoming(0,8,update.getTrackingMethod())
			
		### Ground Station Data Table (usually doesn't change, but I guess it might) ###
		self.updateGround(0,0,groundLat)
		self.updateGround(0,1,groundLon)
		self.updateGround(0,2,groundAlt)
		self.updateGround(0,3,centerBear)

		### Antenna current "intended" position ###
		self.updateGround(0,4,panOffset)
		self.updateGround(0,5,tiltOffset)
		self.updateGround(0,6,antennaBear)
		self.updateGround(0,7,antennaEle)
		
		### Update the Graphs in the Tracker Tab
		if(settingsUpdated and self.graphReal.isChecked()):						# Check to see if you have the graph checkbox selected
			if len(self.receivedAlt) > 0:

				# creates the 4 subplots 
				ALTPLOT = self.figure.add_subplot(221)
				LOSPLOT = self.figure.add_subplot(222)
				ELEPLOT = self.figure.add_subplot(223)
				BEARPLOT = self.figure.add_subplot(224)

				# discards the old graph
				ALTPLOT.hold(False)
				LOSPLOT.hold(False)
				ELEPLOT.hold(False)
				BEARPLOT.hold(False)
				
				# plot data
				ALTPLOT.plot(self.receivedTime-self.receivedTime[0],self.receivedAlt, 'r-')
				ALTPLOT.set_ylabel('Altitude (ft)')
				LOSPLOT.plot(self.receivedTime-self.receivedTime[0],self.losLog,'g-')
				LOSPLOT.set_ylabel('Line-of-Sight (km)')
				ELEPLOT.plot(self.receivedTime-self.receivedTime[0],self.elevationLog, 'b-')
				ELEPLOT.set_ylabel('Elevation Angle')
				BEARPLOT.plot(self.receivedTime-self.receivedTime[0],self.bearingLog,'y-')
				BEARPLOT.set_ylabel('Bearing Angle')

				# refresh canvas
				self.canvas.draw()

	def manualRefresh(self):
		""" Updates the ground station data table """
		### Ground Station Data Table (usually doesn't change, but I guess it might) ###
		self.updateGround(0,0,groundLat)
		self.updateGround(0,1,groundLon)
		self.updateGround(0,2,groundAlt)
		self.updateGround(0,3,centerBear)

		### Antenna current "intended" position ###
		self.updateGround(0,4,panOffset)
		self.updateGround(0,5,tiltOffset)
		self.updateGround(0,6,antennaBear)
		self.updateGround(0,7,antennaEle)

					
	def getSettings(self):
		""" Go through the settings tab and update class and global variables with the new settings """
		global servoAttached, rfdAttached, arduinoAttached
		global settingsUpdated, useIridium, useRFD, useAPRS
		global centerBear, getLocal, manualLocal, centerBearSet
		global groundLat, groundLon, groundAlt
		global s
		global saveData
		global iridiumInterrupt, aprsInterrupt, aprsStarted, iridiumStarted
		global internetAccess, mapMade
		
		settingsUpdated = True		# Used by the refresh function (which is on a timer), to see if you've updated at least once (to basically get started)
		
		### Determine whether or not to save the Data for this flight ###
		if(self.saveDataCheckbox.isChecked()):
			if(not saveData):
				saveData = True
				timestamp = str(datetime.today().strftime("%m-%d-%Y %H-%M-%S"))
				# Files are saved in the Logs folder, with the timestamp first in the name, followed by the description of the type of data the file contains
				self.rfdLog = "Logs/"+timestamp + ' ' + "RFDLOG.txt"
				f = open(self.rfdLog,'w')
				f.close()
				self.stillImageLog = "Logs/"+timestamp + ' ' + "STILLIMAGELOG.txt"
				f = open(self.stillImageLog,'w')
				f.close()
				self.balloonLocationLog = "Logs/"+timestamp + ' ' + "BALLOONLOCATIONLOG.txt"
				f = open(self.balloonLocationLog,'w')
				f.close()
				self.pointingLog = "Logs/"+timestamp + ' ' + "POINTINGLOG.txt"
				f = open(self.pointingLog,'w')
				f.close()
		elif(not self.saveDataCheckbox.isChecked()):
			saveData = False
			
		### Determine if there's internet Access for the maps ###
		if(self.internetCheckBox.isChecked()):
			internetAccess = True
			
			### Set up the Map View ###
			if(not mapMade):
				self.mapView = WebView()
				self.mapView.setHtml(getMapHtml(45,-93))
				self.mapViewGridLayout.addWidget(self.mapView)
			mapMade = True
		else:
			internetAccess = False
		
		### Check to see what COM ports are in use, and assign them their values from the entry boxes ###
		servoAttached = self.servoAttached.isChecked()
		rfdAttached = self.rfdAttached.isChecked()
		arduinoAttached = self.arduinoAttached.isChecked()
		aprsAttached = self.aprsAttached.isChecked()
		# Use the placeholder values if there is nothing entered in the box, but the checkbox says it's connected
		if(self.servoAttached.isChecked()):
			if(not self.servoCOM.text() == ""):
				servoCOM = str(self.servoCOM.text())
				self.servos = SerialDevice(servoCOM,9600,0.5)
				self.setServoAccel()
				self.setServoSpeed()
		if(self.rfdAttached.isChecked()):
			if(not self.rfdCOM.text() == ""):
				rfdCOM = str(self.rfdCOM.text())
				self.RFD = SerialDevice(rfdCOM,38400,2)
		if(self.arduinoAttached.isChecked()):
			if(not self.arduinoCOM.text() == ""):
				arduinoCOM = str(self.arduinoCOM.text())
				self.arduino = SerialDevice(arduinoCOM,115200,5)
		if(self.aprsAttached.isChecked()):
			if(self.aprsCallsign.text() == ""):				# Get the APRS callsign too, default to placeholder
				self.callsign = str(self.aprsCallsign.placeholderText())
			else:
				self.callsign = self.aprsCallsign.text()
			if(not self.aprsCOM.text() == ""):
				aprsCOM = str(self.aprsCOM.text())
				self.APRS = SerialDevice(aprsCOM,9600,5)
				
		# Get the IMEI for the iridium modem, default to placeholder
		if(self.iridiumIMEI.text() == ''):
			self.IMEI = str(self.iridiumIMEI.placeholderText())
		else:
			self.IMEI = str(self.iridiumIMEI.text())
		
		### If Get Local radio button is selected, use the arduino/IMU to get location and center bearing; otherwise get from the manual entry boxes ###
		if(self.getLocal.isChecked()):
			getLocal = True
			manualLocal = False
			if not centerBearSet:			# If the center bearing hasn't been set before, use the arduino to set it
				self.calibrateIMU()
		else:
			manualLocal = True
			getLocal = False
			if(self.bearingNorth.isChecked()):			# North Radio Button
				centerBear = 0
			elif(self.bearingEast.isChecked()):			# East Radio Button
				centerBear = 90
			elif(self.bearingSouth.isChecked()):		# South Radio Button
				centerBear = 180
			elif(self.bearingWest.isChecked()):			# West Radio Button
				centerBear = 270
			else:
				centerBear = 0
				print "Error with manual bearing setup"
			# Get the ground station location from the entry boxes, default to placeholder
			groundLat = self.manualLat.text()
			groundLon = self.manualLon.text()
			groundAlt = self.manualAlt.text()
			if (groundLat == ""):
				groundLat = self.manualLat.placeholderText()
			if (groundLon == ""):
				groundLon = self.manualLon.placeholderText()
			if (groundAlt == ""):
				groundAlt = self.manualAlt.placeholderText()
			groundLat = float(groundLat)
			groundLon = float(groundLon)
			groundAlt = float(groundAlt)

		useIridium = self.autoIridium.isChecked()
		useAPRS = self.autoAPRS.isChecked()
		useRFD = self.autoRFD.isChecked()
		useDisabled = self.autoDisabled.isChecked()

		if(useDisabled):
			useIridium = False
			useAPRS = False
			useRFD = False

		aprsInterrupt = False
		if(useAPRS and not aprsStarted):					# Don't start it up again if it's already going
			if(aprsAttached):
				aprsWorker = Worker(self.getAPRS)				# Create an instance of the Worker class, and pass in the function you need
				aprsWorker.moveToThread(self.aprsThread)		# Move the new class to the thread you created
				aprsWorker.start.emit("hello")					# Start it up and say something to confirm
				aprsWorker.start.connect(aprsWorker.run)
				self.aprsWorker = aprsWorker
				aprsStarted = True
			else:
				self.createWarning('No APRS Attached')
				self.autoAPRS.setChecked(False)
		elif(not useAPRS):
			print("APRS Interrupted")
			aprsInterrupt = True
			aprsStarted = False
			
		### Determine which types of tracking are selected ###
		if(internetAccess):
			### Start up each type of tracking selected ###
			iridiumInterrupt = False
			if(useIridium and not iridiumStarted):					# Don't start it up again if it's already going
				iridiumWorker = Worker(self.getIridium)				# Create an instance of the Worker class, and pass in the function you need
				iridiumWorker.moveToThread(self.iridiumThread)		# Move the new class to the thread you created
				iridiumWorker.start.connect(iridiumWorker.run)
				iridiumWorker.start.emit("hello")						# Start it up and say something to confirm
				self.iridiumWorker = iridiumWorker
				iridiumStarted = True
			elif(not useIridium):
				print("Iridium Interrupted")
				iridiumInterrupt = True
				iridiumStarted = False
		else:
			self.createWarning('Iridium Tracking will not work without Internet Access')
			self.autoIridium.setChecked(False)

		if(self.autoIridium.isChecked() or self.autoAPRS.isChecked() or self.autoRFD.isChecked()):
			self.manualRefresh()
		else:
			self.autoDisabled.setChecked(True)			
			self.manualRefresh()

	def createWarning(self,text):
		""" Creates a warning pop up window that can be dismissed by clicking the button """
		self.warning = QWidget()
		self.warningLabel = QLabel()
		self.warningLabel.setText(text)
		self.warningButton = QPushButton()
		self.warningButton.setText('OK')
		self.warningButton.clicked.connect(lambda: self.deleteWindow(self.warning))
		self.warningLayout = QVBoxLayout()
		self.warningLayout.addWidget(self.warningLabel)
		self.warningLayout.addWidget(self.warningButton)
		self.warning.setLayout(self.warningLayout)
		self.warning.show()

	def deleteWindow(self,window):
		""" Eliminates the window """
		window.deleteLater()
		
	def antennaOnline(self,update):
		""" Reaim the antennae while in autotrack mode """
		global autotrackOnline
		if autotrackOnline:
			self.status.setText("Online")
			self.changeTextColor(self.status,"green")				# Update a nice and pretty status indicator in green
			self.trackerLaunch.setText("Disable Antenna Tracker")
			self.moveToTarget(update.getBear(), update.getEle())			# Move Antenna to correct position
		else:
			#Graphing Arrays - wipe them
			self.receivedTime = []
			self.receivedLat = []
			self.receivedLon = []
			self.receivedAlt = []
			self.losLog = []
			self.elevationLog = []
			self.bearingLog = []
			#Update a nice and pretty status indicator in red
			self.status.setText("Offline")
			self.changeTextColor(self.status,"red")
	
	def manualEntryUpdate(self):
		""" Takes the values from the manual coordinate entry boxes and updates the tracker """
		global groundLat, groundLon, groundAlt
		if self.autoDisabled.isChecked():		# Only allow manual updates of the tracker if autotracking is disabled
			try:
				lat = float(self.ManualEntryLatitude.text())
				lon = float(self.ManualEntryLongitude.text())
				alt = float(self.ManualEntryAltitude.text())
				distance = haversine(groundLat, groundLon, lat, lon)
				bear = bearing(groundLat, groundLon, lat, lon)
				ele = elevationAngle(alt, groundAlt, distance)

				self.moveToTarget(bear,ele)			# Move the tracker
				self.manualRefresh()				# Update the ground station table
				print("Reaimed by Manual Coordinate Entry")

			except:
				print("Error with Manual Coordinate Entry, make sure Latitude, Longitude, and Altitude are entered")

	def manualAngleEntryUpdate(self):
		""" Takes the values from the manual angle entry boxes and updates the tracker """
		if self.autoDisabled.isChecked():		# Only allow manual updates of the tracker if autotracking is disabled
			try:
				bear = float(self.manualEntryBearing.text())
				# Get the bearing between 0 and 360
				while bear < 0:
					bear = bear + 360
				while bear > 360:
					bear = bear - 360
				print(bear)
				
				ele = float(self.manualEntryElevation.text())
				# Get the elevation angle between 0 and 360
				while ele < 0:
					ele = ele + 360
				while ele > 360:
					ele = ele - 360
				print(ele)

				self.moveToTarget(bear,ele)
				self.manualRefresh()
				print("Reaimed by Manual Angle Entry")

			except:
				print("Error with Manual Angle Entry, make sure Bearing and Elevation Angle are entered")
	
	def sliderControl(self,arg):
		""" Control the sliders when you hit the button, or stop it if you hit the button again """
		global inSliderMode
		
		### When the start/stop button is clicked, toggle the state of the sliders ###
		if arg == "click":
			if self.autoDisabled.isChecked():   # Only let this work if you're not in autotrack mode
				if(inSliderMode):				# If you're in slider mode, set the boolean to false, change the text back and get out
					inSliderMode = False
					self.sliderButton.setText("START")
					self.sliderStatus.setText("OFF")
					self.changeTextColor(self.sliderStatus,"red")
					return
				if inSliderMode == False:		# if not in slider mode, change the boolean, text and text color
					print(inSliderMode)
					inSliderMode = True
					print(inSliderMode)
					self.sliderButton.setText("STOP")
					self.sliderStatus.setText("ON")
					self.changeTextColor(self.sliderStatus,"green")
					
		### When a slider position is changed, move the position of the servos ###
		if arg == "slide":
			if(inSliderMode):			# Only move if you're in slider mode
				self.moveToTarget(self.panServoSlider.value(),self.tiltServoSlider.value())
				self.manualRefresh()			# Refresh the data tables
					
	def trimControl(self,arg):
		""" Updates the trim values when the trim buttons are clicked, and move the tracking accordingly """
		global tiltOffset, panOffset, antennaBear, antennaEle
		
		if(arg == 'up'):		# Adds one degrees of trim to the tilt servo
			tiltOffset += 1
			print("Tilt Trim: "+str(tiltOffset))
		elif(arg == 'down'):	# Subtracts one degrees of trim from the tilt servo
			tiltOffset -= 1
			print("Tilt Trim: "+str(tiltOffset))
		elif(arg == 'left'):	# Subtracts one degree of trim from the pan servo
			panOffset -= 1
			print("Pan Trim: "+str(panOffset))
		elif(arg == 'right'):	# Adds one degree of trim to the pan servo
			panOffset += 1
			print("Pan Trim: "+str(panOffset))
		elif(arg == 'reset'):	# Resets the trim values to zero
			tiltOffset = 0
			panOffset = 0
			print("Tilt Trim: "+str(tiltOffset))
			print("Pan Trim: "+str(panOffset))

		self.moveToTarget(antennaBear,antennaEle)			# Move the tracker
		self.manualRefresh()								# Update the ground station table
		
	def toggleStillImageSystem(self):
		""" Toggles the state of the still image system """
		global saveData
		
		if rfdCommandsOnline:		# Don't let this happen if the RFD Commands are still going
			print("RFD Commands are still Online")
			self.stillImageTextBrowser.append("RFD Commands are still Online")
			if(saveData):
				self.logData("stillImage",'newText'+','+'RFD Commands are still Online')
			return
			
		if self.stillImageOnline:		# If the still image system is online, turn it off and change the text
			self.stillImageOnline = False
			self.stillImageOnlineButton.setText("START")
			self.stillImageOnlineLabel.setText("OFF")
			self.changeTextColor(self.stillImageOnlineLabel,"red")
			if saveData:		# Log the toggle
				self.logData("stillImage",'toggle'+','+"Still Image System Turned Off")
			return
		else:						# Otherwise, start the still image system
			if not rfdAttached:
				print("No RFD Radio on this computer")
				self.stillImageTextBrowser.append("No RFD Radio on this Computer")
				if(saveData):
					self.logData('stillImage','newText'+','+'No RFD Radio on this Computer')
				return
			if saveData:		# Log the toggle
				self.logData('stillImage','toggle'+','+"Still Image System Turned On")
			self.stillImageOnline = True
			self.stillImageOnlineButton.setText("STOP")
			self.stillImageOnlineLabel.setText("ON")
			self.changeTextColor(self.stillImageOnlineLabel,"green")
			return
			
	def updateStillImageValues(self):
		""" Updates the still image system slider positions to match the values """
		self.picWidthSlider.setValue(self.picWidth)
		self.picHeightSlider.setValue(self.picHeight)
		self.picSharpSlider.setValue(self.picSharpness)
		self.picBrightSlider.setValue(self.picBrightness)
		self.picContrastSlider.setValue(self.picContrast)
		self.picSaturationSlider.setValue(self.picSaturation)
		self.picISOSlider.setValue(self.picISO)
			
	def updatePicSliderValues(self):
		""" Updates the values displayed for the still image picture control sliders """
		self.picCurrentWidthValue.setText(str(self.picWidthSlider.value()))
		self.picCurrentHeightValue.setText(str(self.picHeightSlider.value()))
		self.picCurrentSharpnessValue.setText(str(self.picSharpSlider.value()))
		self.picCurrentBrightnessValue.setText(str(self.picBrightSlider.value()))
		self.picCurrentContrastValue.setText(str(self.picContrastSlider.value()))
		self.picCurrentSaturationValue.setText(str(self.picSaturationSlider.value()))
		self.picCurrentISOValue.setText(str(self.picISOSlider.value()))
		
	def stillImageButtonPress(self,arg):
		""" Starts the function associate to the button pressed in the worker thread """
		if arg == 'mostRecent':
			rfdWorker = Worker(self.getMostRecentImage)		# Create an instance of the Worker class, and pass in the function you need
			rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit("hello")		# Start it up and say something to confirm
			self.rfdWorker = rfdWorker
			
		if arg == 'selectImage':
			if(self.stillImageOnline):

				### Build the image selection window ###
				self.picSelectionWindow = QWidget()
				self.picSelectionWindow.setWindowTitle("Image Selection")
				self.listbox = QListWidget(self)
				self.picSelectionLabel = QLabel()
				self.picSelectionLabel.setText("Select the Picture to Receive")
				self.picSelectionButton = QPushButton()
				self.picSelectionButton.setText("Select")
				self.picSelectLayout = QVBoxLayout()
				self.picSelectLayout.addWidget(self.picSelectionLabel)
				self.picSelectLayout.addWidget(self.listbox)
				self.picSelectLayout.addWidget(self.picSelectionButton)
				self.picSelectionWindow.setLayout(self.picSelectLayout)
				self.picSelectionWindow.show()
				# Move to the function if they click select
				self.picSelectionButton.clicked.connect(lambda: self.checkRequestedImage(self.listbox.currentItem()))

			rfdWorker = Worker(self.getImageDataTxt)		# Create an instance of the Worker class, and pass in the function you need
			rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit("hello")		# Start it up and say something to confirm
			self.rfdWorker = rfdWorker
			
		if arg == 'getPicSettings':
			rfdWorker = Worker(self.picGetSettings)		# Create an instance of the Worker class, and pass in the function you need
			rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit("hello")		# Start it up and say something to confirm
			self.rfdWorker = rfdWorker
			
		if arg == 'sendNewSettings':
			rfdWorker = Worker(self.picSendNewSettings)		# Create an instance of the Worker class, and pass in the function you need
			rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit("hello")		# Start it up and say something to confirm
			self.rfdWorker = rfdWorker
			
		if arg == 'HFlip':
			rfdWorker = Worker(self.picHorizontalFlip)
			rfdWorker.moveToThread(self.rfdThread)
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit('hello')
			self.rfdWorker = rfdWorker
			
		if arg == 'VFlip':
			rfdWorker = Worker(self.picVerticalFlip)
			rfdWorker.moveToThread(self.rfdThread)
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit('hello')
			self.rfdWorker = rfdWorker
			
		if arg == 'timeSync':
			rfdWorker = Worker(self.time_sync)		# Create an instance of the Worker class, and pass in the function you need
			rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
			rfdWorker.start.connect(rfdWorker.run)
			rfdWorker.start.emit("hello")		# Start it up and say something to confirm
			self.rfdWorker = rfdWorker

	def updateStillImageSystemText(self,text):
		""" Updates the still image system text browser with the text passed in as the argument """
		self.stillImageTextBrowser.append(text)
		if saveData:									# If data logging is on, log the new text
			self.logData('stillImage','newText'+','+text)
			
	def updatePicture(self,displayPath):
		""" Updates the still image system picture display to the picture associated with the path passed in as the argument """
		print("Updating Picture")
		pm = QPixmap(str(displayPath))		# Create a pixmap from the default image
		scaledPm = pm.scaled(self.picLabel.size(),QtCore.Qt.KeepAspectRatio,QtCore.Qt.SmoothTransformation)		# Scale the pixmap
		self.picLabel.setPixmap(scaledPm)			# Set the label to the map
		self.picLabel.show()				# Show the image
		if saveData:						# If data logging is on, log the new path
			self.logData('stillImage','newPic'+','+displayPath)
			
	def updatePictureProgress(self,progress,maxProgress):
		""" Updates the still image system photo progress bar based on the value and max value passed in as arguments """
		self.photoProgressBar.setMaximum(maxProgress)
		self.photoProgressBar.setValue(progress)
		
	def getMostRecentImage(self):
		""" Still Image System: Get the Most Recent Image through the RFD 900 """
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			self.rfdThread.newStillText.emit("Still Image System not Online")
			print("Still Image System not Online")
			return
			
		if(rfdAttached):	# Only try to do stuff if there's an RFD attached
			rfdSer = self.RFD.getDevice()
			
			### Write 1 until you get the acknowledge back ###
			rfdSer.write('1')
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):			# Make sure you don't print out a huge stream if you get the wrong response
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				sys.stdout.flush()
				rfdSer.write('1')
				
			### Make the file name by reading the radio ###
			sendfilename = ""
			temp = 0
			while(temp <= 14):
				sendfilename += str(rfdSer.read())
				temp += 1

			### Get the image path name from the entry box, or create it if there's nothing entered ###
			imagepath = self.requestedImageName.text()
			if (imagepath == ""):
				try:
					if(sendfilename[0] == "i"):
						imagepath = sendfilename
					else:
						imagepath = "image_%s%s" % (str(datetime.today().strftime("%Y%m%d_T%H%M%S")),self.extension)
				except:
					imagepath = "image_%s%s" % (str(datetime.today().strftime("%Y%m%d_T%H%M%S")),self.extension)
			else:
				imagepath = imagepath+self.extension
			print "Image will be saved as:", imagepath
			self.rfdThread.newStillText.emit("Image will be saved as: " + imagepath)
			
			### Receive the Image ###
			timecheck = time.time()
			sys.stdout.flush()
			self.receive_image(str(imagepath), self.wordlength, rfdSer)			# Get the picture
			print "Receive Time =", (time.time() - timecheck)
			self.rfdThread.newStillText.emit("Receive Time = " + str((time.time() - timecheck)))
			
			### Clean Up and Exit ###
			self.rfdThread.newProgress.emit(0,1)		# Reset the progress bar to empty
			sys.stdout.flush()							# Clear the buffer
			rfdSer.close()								# Close the RFD Serial Port
			return
			
		else:	# If there's no RFD, print the message and get out
			print("No RFD Radio on this computer")
			self.rfdThread.newStillText.emit("No RFD Radio on this Computer")
			return

	def getImageDataTxt(self):
		"""
		Still Image System: Requests imagedata.txt, for the purpose 
		of selecting a specific image to download 
		"""
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit("Still Image System not Online")
			return
			
		if(rfdAttached):	# Only try to do stuff if there's an RFD attached
			rfdSer = self.RFD.getDevice()
			
			### Send the Pi 2 until the acknowledge is received ###
			rfdSer.write('2')
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):				# Make sure you don't print out a huge stream if the wrong thing is received
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				sys.stdout.flush()
				rfdSer.write('2')
			
			### Use the entry box to get the name of the file, or fall back to the placeholder name ###
			try:
				f = open('imagedata'+".txt","w")
			except:		# Return if there's an error opening the file
				print "Error with Opening File"
				self.rfdThread.newStillText.emit("Error with Opening File")
				sys.stdout.flush()
				return
				
			### Read each line that received from the RFD, and write them to the file ###
			timecheck = time.time()
			temp = rfdSer.readline()
			while(temp != ""):
				f.write(temp)
				try:
					self.listbox.addItem(temp)
				except:
					print "Error Adding Items"
					self.rfdThread.newStillText.emit("Error Adding Items")
					break
				temp = rfdSer.readline()
			f.close()
			
			rfdSer.close()
			
			return
			
		else:	# If there's no RFD, print the message and get out
			print("No RFD Radio on this computer")
			self.rfdThread.newStillText.emit("No RFD Radio on this Computer")
			return
			
	def checkRequestedImage(self,pic):
		""" Still Image System: Make sure the user doesn't accidentally get a high res image """
		
		data = pic.text()
		if (data[10] != 'b'):										# High Res images are marked with a b
			self.rfdThread.requestConfirmation.emit(str(data))			# Emit the signal to get a confirmation				
		else:
			self.getRequestedImageHelper(str(data))						# Go ahead and download the picture
			
	def getRequestedImageHelper(self,data):
		""" Starts gettings the requested image in the rfd thread """
		
		# Get rid of the confirmation window if it's there
		try:
			self.confirmationCheckWindow.deleteLater()
		except:
			print("No window to delete, or failed to delete window")
		
		rfdWorker = Worker(lambda: self.getRequestedImage(data))		# Create an instance of the Worker class, and pass in the function you need
		rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
		rfdWorker.start.connect(rfdWorker.run)
		rfdWorker.start.emit("hello")		# Start it up and say something to confirm
		self.rfdWorker = rfdWorker

	def getRequestedImage(self,data):
		""" Still Image System: Retrieves the image specified in the argument, deletes the confirmation window if necessary """

		rfdSer = self.RFD.getDevice()

		### Continuously write 3 until the acknowledge is received ###
		rfdSer.write('3')
		timeCheck = time.time() + 1
		while (rfdSer.read() != 'A'):
			if(timeCheck < time.time()):			# Make sure you don't emit a huge stream of messages if the wrong this is received
				print "Waiting for Acknowledge"
				self.rfdThread.newStillText.emit("Waiting for Acknowledge")
				timeCheck = time.time() + 1
			sys.stdout.flush()
			rfdSer.write('3')
		# self.sync(rfdSer)							# Syncronize the data streams of the ground station and the Pi before starting
		imagepath = data[0:15]
		rfdSer.write(data)				# Tell the pi which picture you want to download
		timecheck = time.time()
		print "Image will be saved as:", imagepath
		self.rfdThread.newStillText.emit("Image will be saved as: " + str(imagepath))
		sys.stdout.flush()
		self.receive_image(str(imagepath), self.wordlength, rfdSer)			# Receive the image
		print "Receive Time =", (time.time() - timecheck)
		self.rfdThread.newStillText.emit("Receive Time = " + str((time.time() - timecheck)))
		self.rfdThread.newProgress.emit(0,1)			# Reset the progress bar

		rfdSer.close()				# Close the RFD serial port

		return

	def highResConfirmationCheck(self,data):
		""" 
		Creates a window a yes and no button prompting the user for confirmation before downloading
		the high resolution image. Interprets the button presses.
		"""

		### Create the window, with text and buttons ###
		self.confirmationCheckWindow = QWidget()
		self.confirmationLabel = QLabel()
		self.confirmationLabel.setText("WARNING! You have selected a high resolution image! Are you sure you want to download?")
		self.confirmationYesButton = QPushButton()
		self.confirmationNoButton = QPushButton()
		self.confirmationYesButton.setText("Yes")
		self.confirmationNoButton.setText("No")
		self.confirmationHLayout = QHBoxLayout()
		self.confirmationVLayout = QVBoxLayout()
		self.confirmationHLayout.addWidget(self.confirmationYesButton)
		self.confirmationHLayout.addWidget(self.confirmationNoButton)
		self.confirmationVLayout.addWidget(self.confirmationLabel)
		self.confirmationVLayout.addLayout(self.confirmationHLayout)
		self.confirmationCheckWindow.setLayout(self.confirmationVLayout)
		self.confirmationCheckWindow.show()

		### Connect the buttons to the functions ###
		self.confirmationYesButton.clicked.connect(lambda: self.getRequestedImageHelper(data))
		self.confirmationNoButton.clicked.connect(lambda: self.deleteWindow(self.confirmationCheckWindow))
		self.confirmationNoButton.clicked.connect(lambda: self.deleteWindow(self.picSelectionWindow))
			
	def picGetSettings(self):
		""" Still Image System: Retrieve Current Camera Settings """
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit("Still Image System not Online")
			return
			
		if(rfdAttached):	# Only try to do stuff if there's an RFD attached
			rfdSer = self.RFD.getDevice()
			
			print "Retrieving Camera Settings"
			self.rfdThread.newStillText.emit("Retrieving Camera Settings")
			killtime = time.time()+10  			# A timeout for the loop so you don't get stuck
			
			### Send the Pi 4 until the acknowledge is received ###
			rfdSer.write('4')
			timeCheck = time.time()
			while ((rfdSer.read() != 'A') & (time.time()<killtime)):
				if(timeCheck < time.time() + 1):					# Make sure you don't print out a huge stream if you get the wrong response
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() +  1
				rfdSer.write('4')
			timecheck = time.time()
			
			### Open the file camerasettings.txt in write mode, and write everything the Pi is sending ###
			try:
				file = open("camerasettings.txt","w")
				print "File Successfully Created"
				self.rfdThread.newStillText.emit("File Successfully Created")
			except:				# If there's an error opening the file, print the message and return
				print "Error with Opening File"
				self.rfdThread.newStillText.emit("Error with Opening File")
				sys.stdout.flush()
				rfdSer.close()
				return
			timecheck = time.time()
			sys.stdin.flush()				# Clear the buffer
			temp = rfdSer.read()
			while((temp != "\r") & (temp != "") ):		# Write everything the radio is receiving to the file
				file.write(temp)
				temp = rfdSer.read()
			file.close()
			print "Receive Time =", (time.time() - timecheck)
			self.rfdThread.newStillText.emit("Receive Time = " + str((time.time() - timecheck)))
			sys.stdout.flush()
			
			### Open the file camerasettings.txt in read mode, and confirm/set the globals based on what's in the settings file ###
			try:
				file = open("camerasettings.txt","r")
				twidth = file.readline()			 #Default = (650,450); range up to
				self.picWidth = int(twidth)
				print("Width = " + str(self.picWidth))
				self.rfdThread.newStillText.emit("Width = " + str(self.picWidth))
				theight = file.readline()			 #Default = (650,450); range up to
				self.picHeight = int(theight)
				print("Height = " + str(self.picHeight))
				self.rfdThread.newStillText.emit("Height = " + str(self.picHeight))
				tsharpness = file.readline()			  #Default  =0; range = (-100 to 100)
				self.picSharpness = int(tsharpness)
				print("Sharpness = " + str(self.picSharpness))
				self.rfdThread.newStillText.emit("Sharpness = " + str(self.picSharpness))
				tbrightness = file.readline()			 #Default = 50; range = (0 to 100)
				self.picBrightness = int(tbrightness)
				print("Brightness = " + str(self.picBrightness))
				self.rfdThread.newStillText.emit("Brightness = " + str(self.picBrightness))
				tcontrast = file.readline()			   #Default = 0; range = (-100 to 100)
				self.picContrast = int(tcontrast)
				print("Contrast = " + str(self.picContrast))
				self.rfdThread.newStillText.emit("Contrast = " + str(self.picContrast))
				tsaturation = file.readline()			 #Default = 0; range = (-100 to 100)
				self.picSaturation = int(tsaturation)
				print("Saturation = " + str(self.picSaturation))
				self.rfdThread.newStillText.emit("Saturation = " + str(self.picSaturation))
				tiso = file.readline()					  #Unknown Default; range = (100 to 800)
				self.picISO = int(tiso)
				print("ISO = " + str(self.picISO))
				self.rfdThread.newStillText.emit("ISO = " + str(self.picISO))
				file.close()
				self.rfdThread.newPicSliderValues.emit()
			except:
				print "Camera Setting Retrieval Error"
				self.rfdThread.newStillText.emit("Camera Setting Retrieval Error")
			
			rfdSer.close()				# Close the RFD Serial Port
			return
			
		else:	# If there's no RFD, print the message and get out
			print("No RFD Radio on this computer")
			self.rfdThread.newStillText.emit("No RFD Radio on this Computer")
			return
			
	def picSendNewSettings(self):
		""" Still Image System: Send New Camera Settings to the Pi """
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit("Still Image System not Online")
			return
			
		if(rfdAttached):	#Only try to do stuff if there's an RFD Attached
			rfdSer = self.RFD.getDevice()
			
			### Update the global values based on current slider position ###
			self.picWidth = int(self.picWidthSlider.value())
			self.picHeight = int(self.picHeightSlider.value())
			self.picSharpness = int(self.picSharpSlider.value())
			self.picBrightness = int(self.picBrightSlider.value())
			self.picContrast = int(self.picContrastSlider.value())
			self.picSaturation = int(self.picSaturationSlider.value())
			self.picISO = int(self.picISOSlider.value())
			
			### Open the camerasettings.txt file, and record the new values ###
			file = open("camerasettings.txt","w")
			file.write(str(self.picWidth)+"\n")
			file.write(str(self.picHeight)+"\n")
			file.write(str(self.picSharpness)+"\n")
			file.write(str(self.picBrightness)+"\n")
			file.write(str(self.picContrast)+"\n")
			file.write(str(self.picSaturation)+"\n")
			file.write(str(self.picISO)+"\n")
			file.close()
			
			### Continue sending 5 until the acknowledge is received from the Pi ###
			rfdSer.write('5')
			timeCheck = time.time() + 1
			termtime = time.time() + 10
			while (rfdSer.read() != 'A' and time.time() < termtime):
				if(timeCheck < time.time()):
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				rfdSer.write('5')
				timecheck = time.time()
			
			### Open the camerasettings.txt file in read mode, and send each line to the Pi ###
			try:
				file = open("camerasettings.txt","r")
			except:
				print "Error with Opening File"
				self.rfdThread.newStillText.emit("Error with Opening File")
				sys.stdout.flush()
				rfdSer.close()
				return
			timecheck = time.time()
			temp = file.readline()
			time.sleep(0.5)
			while(temp != ""):
				rfdSer.write(temp)
				temp = file.readline()
			file.close()
			
			### Send the Pi A until the acknowledge is received, or until too much time has passed ###
			error = time.time()
			while (rfdSer.read() != 'A'):			# Make sure you don't print out a huge stream if you get the wrong response
				if(timeCheck < time.time()):
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				sys.stdout.flush()
				if(error+10<time.time()):
					print "Acknowledge not Received"
					self.rfdThread.newStillText.emit("Acknowledge not Received")
					return
				print "Send Time =", (time.time() - timecheck)
			self.rfdThread.newStillText.emit("Send Time =" + str((time.time() - timecheck)))
			
			sys.stdout.flush()			# Clear the buffer
			rfdSer.close()				# Close the RFD Serial Port
			return
			
		else:	# If there's no RFD, print the message and get out
			print("No RFD Radio on this computer")
			self.rfdThread.newStillText.emit("No RFD Radio on this Computer")
			return
			
	def picDefaultSettings(self):
		""" Still Image System: Sets the camera variables to the default values """
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.stillImageTextBrowser.append("Still Image System not Online")
			return
			
		### Default Picture Settings ###
		width = 650
		height = 450
		sharpness = 0			#Default  =0; range = (-100 to 100)
		brightness = 50			#Default = 50; range = (0 to 100)
		contrast = 0			#Default = 0; range = (-100 to 100)
		saturation = 0			#Default = 0; range = (-100 to 100)
		iso = 400				#Unknown Default; range = (100 to 800)


		### Print/write to the browser what you're doing ###
		print "Default width:",width
		self.stillImageTextBrowser.append("Default Width: " + str(width))
		print "Default height:",height
		self.stillImageTextBrowser.append("Default Height: " + str(height))
		print "Default sharpness:",sharpness
		self.stillImageTextBrowser.append("Default Sharpness: " + str(sharpness))
		print "Default brightness:",brightness
		self.stillImageTextBrowser.append("Default Brightness: " + str(brightness))
		print "Default contrast:",contrast
		self.stillImageTextBrowser.append("Default Contrast: " + str(contrast))
		print "Default saturation:",saturation
		self.stillImageTextBrowser.append("Default Saturation: " + str(saturation))
		print "Default ISO:",iso
		self.stillImageTextBrowser.append("Default ISO: " + str(iso))
		sys.stdout.flush()			# Clear the buffer
		
		### Change the slider values ###
		self.picWidthSlider.setValue(width)
		self.picHeightSlider.setValue(height)
		self.picSharpSlider.setValue(sharpness)
		self.picBrightSlider.setValue(brightness)
		self.picContrastSlider.setValue(contrast)
		self.picSaturationSlider.setValue(saturation)
		self.picISOSlider.setValue(iso)
		
		### Update the Values ###
		self.picWidth = width
		self.picHeight = height
		self.picSharpness = sharpness
		self.picBrightness = brightness
		self.picContrast = contrast
		self.picSaturation = saturation
		self.picISO = iso
		
		return
		
	def picVerticalFlip(self):
		""" Still Image System: Flips the image vertically """
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit("Still Image System not Online")
			return
		
		if(rfdAttached):
			rfdSer = self.RFD.getDevice()
			
			### Send the pi 0 until the acknowledge is received, or until too much time has passed ###
			rfdSer.write('0')
			termtime = time.time() + 10
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):
					print("Waiting for Acknowledge")
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				rfdSer.write('0')
				if(termtime < time.time()):
					print("No Acknowldeg Received, Connection Error")
					self.rfdThread.newStillText.emit("No Acknowledge Received, Connect Error")
					sys.stdout.flush()
					return
					
			print("Camera Vertically Flipped")
			self.rfdThread.newStillText.emit("Camera Vertically Flipped")
			
	def picHorizontalFlip(self):
		""" Still Image System: Flips the image Horizontally """
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit("Still Image System not Online")
			return
		
		if(rfdAttached):
			rfdSer = self.RFD.getDevice()
			
			### Send the pi 9 until the acknowledge is received, or until too much time has passed ###
			rfdSer.write('9')
			termtime = time.time() + 10
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):
					print("Waiting for Acknowledge")
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				rfdSer.write('9')
				if(termtime < time.time()):
					print("No Acknowldeg Received, Connection Error")
					self.rfdThread.newStillText.emit("No Acknowledge Received, Connect Error")
					sys.stdout.flush()
					return
					
			print("Camera Horizontally Flipped")
			self.rfdThread.newStillText.emit("Camera Horizontally Flipped")
			
		
	def time_sync(self):
		""" Still Image System: Syncronizes the Pi and ground station so that the connection test can be run """
		
		# Check if the Still Image System is online
		if not self.stillImageOnline:
			print("Still Image System not Online")
			self.rfdThread.newStillText.emit('Still Image System not Online')
			return
		
		if(rfdAttached):	# Only try to do stuff if there's a RFD Attached
			rfdSer = self.RFD.getDevice()

			### Send the Pi T until the acknowledge is received, or until the too much time has passed ###
			rfdSer.write('8')
			termtime = time.time() + 20
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):
					print "Waiting for Acknowledge"
					self.rfdThread.newStillText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				rfdSer.write('8')
				if (termtime < time.time()):	# If too much time has passed, let the user know and return
					print "No Acknowledge Received, Connection Error"
					self.rfdThread.newStillText.emit('No Acknowledge Received, Connection Error')
					sys.stdout.flush()
					return
			
			### Display the time on the Pi and the local time ###
			localtime = str(datetime.today().strftime("%m/%d/%Y %H:%M:%S"))
			rasptime = str(rfdSer.readline())
			print "##################################\nRaspb Time = %s\nLocal Time = %s\n##################################" % (rasptime,localtime)
			self.rfdThread.newStillText.emit("##################################\nRaspb Time = %s\nLocal Time = %s\n##################################" % (rasptime,localtime))
			sys.stdin.flush()
			
			#Run the connection test
			self.connectiontest(10, rfdSer)
			
			rfdSer.close()			# Close the RFD Serial Port
			return
			
		else:	# If there's no RFD, print the message and get out
			print("No RFD Radio on this computer")
			self.stillImageTextBrowser.append("No RFD Radio on this computer")
			return
			
	def receive_image(self, savepath, wordlength, rfdPort):
		""" Receive an Image through the RFD 900 """
								
		rfdSer = rfdPort		# Rename the RFD serial port to the normal thing
		
		print "Confirmed photo request"		#Notifies User we have entered the receiveimage() module
		self.rfdThread.newStillText.emit("Confirmed photo request")
		sys.stdout.flush()
		
		### Module Specific Variables ###
		trycnt = 0				#Initializes the checksum timeout (timeout value is not set here)
		finalstring = ""		#Initializes the data string so that the += function can be used
		done = False			#Initializes the end condition
		
		### Setup the Progress Bar ###
		try:
			photoSize = rfdSer.readline()			# The first thing you get is the total picture size so you can make the progress bar
			print("Total Picture Size: ",photoSize)
			self.rfdThread.newStillText.emit("Total Picture Size: " + photoSize)
			stillPhotoMax = int(photoSize)
			stillProgress = 0
			self.rfdThread.newProgress.emit(stillProgress,stillPhotoMax)
		except:
			print("Error retrieving picture size")
			self.rfdThread.newStillText.emit("Error retrieving picture size")
		
		### Retreive Data Loop (Will end when on timeout) ###
		while(done == False):
			print "Current Receive Position: ", str(len(finalstring))
			self.rfdThread.newStillText.emit("Current Received Position: "+ str(len(finalstring)))
			checktheirs = ""
			checktheirs = rfdSer.read(32)		#Asks first for checksum. Checksum is asked for first so that if data is less than wordlength, it won't error out the checksum data
			word = rfdSer.read(wordlength)		#Retreives characters, who's total string length is predetermined by variable wordlength
			checkours = gen_checksum(word)		#Retreives a checksum based on the received data string
			
			#CHECKSUM
			if (checkours != checktheirs):
				if(trycnt < 5):		#This line sets the maximum number of checksum resends. Ex. trycnt = 5 will attempt to rereceive data 5 times before erroring out											  #I've found that the main cause of checksum errors is a bit drop or add desync, this adds a 2 second delay and resyncs both systems 
					rfdSer.write('N')
					trycnt += 1
					print "try number:", str(trycnt)
					self.rfdThread.newStillText.emit("try number: "+str(trycnt))
					print "\tresend last"		#This line is mostly used for troubleshooting, allows user to view that both devices are at the same position when a checksum error occurs
					self.rfdThread.newStillText.emit("\tresent last")
					print "\tpos @" , str(len(finalstring))
					self.rfdThread.newStillText.emit("\tpos @ "+ str(len(finalstring)))
					print "\twordlength", str(wordlength)
					self.rfdThread.newStillText.emit("\twordlength "+str(wordlength))
					sys.stdout.flush()
					if wordlength >1000:
						wordlength -= 1000
					self.sync(rfdSer)		#This corrects for bit deficits or excesses ######  THIS IS A MUST FOR DATA TRANSMISSION WITH THE RFD900s!!!! #####
				else:
					rfdSer.write('N')		#Kind of a worst case, checksum trycnt is reached and so we save the image and end the receive, a partial image will render if enough data
					finalstring += word								 
					done = True
					break
			else:							# If everything goes well, reset the try counter, and add the word to the accumulating final wor
				trycnt = 0
				rfdSer.write('Y')
				finalstring += str(word)
				stillProgress += wordlength
				self.rfdThread.newProgress.emit(stillProgress,stillPhotoMax)
			if(len(finalstring) % 1000 != 0):			# The words always come in increments of some thousand, so if it's not evenly divisible, you're probably at the end
				done = True
				break
		### Save the image as the given filename in the Images folder
		try:
			b64_to_image(finalstring,"Images/"+str(savepath))			# Decode the image
			self.displayPhotoPath = "Images/"+str(savepath)
			self.rfdThread.newPicture.emit(self.displayPhotoPath)		# Send the signal with the new image location to the main GUI
		except:
			print "Error with filename, saved as newimage" + self.extension
			self.rfdThread.newStillText.emit("Error with filename, saved as newimage" + self.extension)
			sys.stdout.flush()
			b64_to_image(finalstring,"Images/"+"newimage" + self.extension)			#Save image as newimage.jpg due to a naming error in the Images folder
		
		### Clean Up ###
		self.wordlength = 7000			# Reset the wordlength to the original
		print "Image Saved"
		self.rfdThread.newStillText.emit("Image Saved")
		sys.stdout.flush()
		
	def sync(self, rfdPort):
		""" Ensures both sender and receiver are at that the same point in their data streams """

		rfdSer = rfdPort			# Rename the RFD serial object to the usual thing
		
		# Prepare to sync by resetting variables
		print "Attempting to Sync - This should take approx. 2 sec"
		self.rfdThread.newStillText.emit("Attempting to Sync - This should take approx. 2 sec")
		sync = ""
		addsync0 = ""
		addsync1 = ""
		addsync2 = ""
		addsync3 = ""
		
		### Program is held until no data is being sent (timeout) or until the pattern 's' 'y' 'n' 'c' is found ###
		while(sync != "sync"):
			addsync0 = rfdSer.read()
			addsync0 = str(addsync0)
			if(addsync0 == ''):
				break
			sync = addsync3 + addsync2 + addsync1 + addsync0
			addsync3 = addsync2
			addsync2 = addsync1
			addsync1 = addsync0
			sync = ""
		rfdSer.write('S')		#Notifies sender that the receiving end is now synced 
		print "System Match"
		self.rfdThread.newStillText.emit("System Match")
		rfdSer.flushInput()			# Clear the buffers to be ready
		rfdSer.flushOutput()
		return

	def connectiontest(self, numping, rfdPort):
		""" Determines the ping time between the Pi and the computer """
		global stillImageBrowserText, newStillText
		
		rfdSer = rfdPort			# Rename the RFD Serial object to the usual thing
		
		### Send the Pi A until the acknowledge is received, or too much time has passed ###
		rfdSer.write('6')
		termtime = time.time() + 20
		while (rfdSer.read() != 'A'):
			self.rfdThread.newStillText.emit("Waiting for Acknowledge")
			print "Waiting for Acknowledge"
			rfdSer.write('6')
			if (termtime < time.time()):	# If too much time passed, let the user know and return
				print "No Acknowledge Received, Connection Error"
				self.rfdThread.newStillText.emit("No Acknowledge Received, Connection Error")
				sys.stdout.flush()
				return
		avg = 0
		
		### Using the specifified number of pings, give the Pi 10 seconds per ping to respond correctly, and record the times ###
		rfdSer.write('~')
		temp = ""
		for x in range (1,numping):
			sendtime = time.time()
			receivetime = 0
			termtime = sendtime + 10
			while ((temp != '~')&(time.time()<termtime)):	# Loop until you get a P back, or too much time has passed
				rfdSer.write('~')
				temp = rfdSer.read()
				receivetime = time.time()
				if (receivetime == 0):	# If too much time has passed and no valid response, print the error, write D, and return
					print "Connection Error, No return ping within 10 seconds"
					self.rfdThread.newStillText.emit("Connection Error, No return ping within 10 seconds")
					rfdSer.write('D')
					sys.stdout.flush()
					return
			else:	# Otherwise reset the temp variable, and accumulate the avg
				temp = ""
				avg += receivetime - sendtime
				#print (avg/x)
		rfdSer.write('D')
		
		### Determine and print the average response time ###
		avg = avg/numping
		print "Ping Response Time = " + str(avg)[0:4] + " seconds"
		self.rfdThread.newStillText.emit("Ping Response Time = " + str(avg)[0:4] + " seconds")
		sys.stdout.flush()			# Clear the buffer
		return
		
	def resizePicture(self,event):
		pm = QPixmap(self.displayPhotoPath)		# Create a pixmap from the default image
		scaledPm = pm.scaled(self.picLabel.size(),QtCore.Qt.KeepAspectRatio,QtCore.Qt.SmoothTransformation)		# Scale the pixmap
		self.picLabel.setPixmap(scaledPm)			# Set the label to the map
		self.picLabel.show()				# Show the image
		
	def rfdListenButtonPress(self):
		""" Receives the press of the listen button, and handles it """
		global rfdCommandsOnline, rfdListenOnline, listenInterrupt, commandInterrupt
		global saveData

		if not rfdCommandsOnline:			# Don't let the listen be messed with while the commands are still running
			if not rfdListenOnline:			# If listening isn't on, turn it on
				rfdListenOnline = True
				self.rfdListenCheck()		# Function to actually make things happen
				
			else:
				listenInterrupt = True 		# Interrupt the listen loop to get out of it
				rfdListenOnline = False 
				self.rfdListenCheck()		# Function to actually make things happen

		else:
			return
		
	def rfdListenCheck(self):
		""" Takes care of the listen starting and stopping, makes sure there are not bad interactions with the commands or other RFD stuff """
		global rfdListenOnline, listenInterrupt

		if(rfdListenOnline):
			if self.stillImageOnline:		# Don't let this work if the still image system is using the RFD 900
				print("Still Image System cannot be Online")
				self.rfdReceiveBrowser.append("Still Image System cannot be Online")
				rfdListenOnline = False
				if(saveData):
					self.logData("RFD","newText"+','+"Still Image System cannot be Online")
				return

			if rfdAttached:				# Only try to do things if the RFD is attached
				self.rfdListenButton.setText("Stop Listening")		# Update the button text and label color
				self.rfdListenOnlineLabel.setText("ON")
				self.changeTextColor(self.rfdListenOnlineLabel,"green")
				listenInterrupt = False 	# Make sure the interrupt is off and ready to use
				if saveData:				# Log the toggle
					self.logData("RFD","toggle"+','+"RFD Listen Online")

				# Starts the rfdListen function in the side thread so that it doesn't interrupt the main loop
				rfdWorker = Worker(self.rfdListen)		# Create an instance of the Worker class, and pass in the function you need
				rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
				rfdWorker.start.connect(rfdWorker.run)
				rfdWorker.start.emit("hello")		# Start it up and say something to confirm
				self.rfdWorker = rfdWorker
			else:
				rfdListenOnline = False
				self.rfdReceiveBrowser.append("No RFD Radio attached")
				if(saveData):
					self.logData("RFD","newText"+','+"No RFD Radio attached")
				
		else:
			# Turn off the RFD listen, and change the button and label text and color
			listenInterrupt = True
			self.rfdListenButton.setText("Listen")
			self.rfdListenOnlineLabel.setText("OFF")
			self.changeTextColor(self.rfdListenOnlineLabel,"red")
			if saveData:
				self.logData("RFD",'toggle'+','+"RFD Listen Offline")
			return

	def rfdListen(self):
		""" Listens to the RFD serial port until interrupted """
		global rfdCommandsOnline, commandInterrupt
		global listenInterrupt, rfdListenOnline
		global saveData, useRFD
		
		if(rfdListenOnline):		# Confirm that the listen is online
			if(rfdAttached):		# Make sure there's still an RFD
				rfdSer = self.RFD.getDevice()
				
				### Loop until interrupted; handle anything received by the RFD ###
				while(not listenInterrupt):
					line = str(rfdSer.readline())
					if(line != ''):				# Send the line to the text browser if it's not empty
						self.rfdThread.newCommandText.emit(datetime.today().strftime('%H:%M:%S') + " || "+line)
					self.rfdThread.payloadUpdate.emit(line)			# Send it to the payload manager
					if(line[0:3] == "GPS" and len(line[4:].split(','))==7):		# If the line received has the GPS identifier, handle it as a newly received RFD balloon location update
						# print(line[0:3],line[4:])
						line = line.split(',')
						line[0] = line[0][4:]
						if(useRFD):
							self.getRFD(line)

				### Clean Up after being Interrupted ###
				listenInterrupt = False 		# Reset the interrupt
				rfdSer.flushInput()				# We don't care about what the RFD is still trying to read after being interrupted
				rfdSer.close()					# Close the RFD serial port
			
	def rfdCommandsButtonPress(self):
		""" Toggles the state of the RFD Commands """
		global rfdCommandsOnline, commandInterrupt, rfdListenOnline, listenInterrupt
		
		if not rfdListenOnline:						# Don't let this be turned on unless Listen is off
		
			### If the commands aren't online, turn them online, and change the text/color of the label and button ###
			if not rfdCommandsOnline:
				if self.stillImageOnline:		# Don't let this work if the still image system is using the RFD 900
					print("Still Image System cannot be Online")
					self.rfdReceiveBrowser.append("Still Image System cannot be Online")
					if(saveData):
						self.logData('RFD','newText'+','+"Still Image System cannot be Online")
					return
				if rfdAttached:		# Only try to do things if the RFD is attached	
					rfdCommandsOnline = True
					if saveData:		# Log the toggle
						self.logData("RFD",'toggle'+','+'RFD Commands Online')
					self.rfdCommandButton.setText("STOP")		# Change the button and label to opposite state
					self.rfdCommandsOnlineLabel.setText("ON")
					self.changeTextColor(self.rfdCommandsOnlineLabel,"green")
						
					# Start up the rfdCommandsControl function in the worker thread so that it doesn't get in the way of the main loop
					rfdWorker = Worker(self.rfdCommandsControl)		# Create an instance of the Worker class, and pass in the function you need
					rfdWorker.moveToThread(self.rfdThread)		# Move the new class to the thread you created
					rfdWorker.start.connect(rfdWorker.run)
					rfdWorker.start.emit("hello")		# Start it up and say something to confirm
					self.rfdWorker = rfdWorker

				else:		# If no RFD, let the user know and return
					print("No RFD Radio attached to this Computer")
					self.rfdReceiveBrowser.append("No RFD Radio attached to this Computer")
					if(saveData):
						self.logData('RFD','newText'+','+'No RFD Radio attached to this Computer')
					return
			else:
				### Turn off the RFD Commands, and change the button and label text and color ###
				commandInterrupt = True
				rfdCommandsOnline = False
				if saveData:		# Log the toggle
					self.logData("RFD",'toggle'+','+"RFD Commands Offline")
				self.rfdCommandButton.setText("START")
				self.rfdCommandsOnlineLabel.setText("OFF")
				self.changeTextColor(self.rfdCommandsOnlineLabel,"red")
		
	def rfdCommandsControl(self):
		""" Handles the RFD Commands """
		global rfdCommandsOnline, commandInterrupt

		if rfdCommandsOnline:		# Make sure the commands are online
			if(rfdAttached):		# Only try to do stuff if there's an RFD Attached
				
				### Collect and create the string ###
				identifier = str(self.rfdIDEntry.text())
				command = str(self.rfdCommandEntry.text())
				if identifier == '' or command == '':		# Don't send null strings
					print("Null strings not allowed")
					self.rfdThread.newCommandText.emit("Null strings not allowed")
					rfdCommandsOnline = False
					self.rfdCommandButton.setText("START")
					self.rfdCommandsOnlineLabel.setText("OFF")
					self.changeTextColor(self.rfdCommandsOnlineLabel,"red")
					return
				toSend = identifier + "?" + command	+ "!"	# Connect the identifier and the command with a ? separating for parsing, and an ! at the end
				
				rfdSer = self.RFD.getDevice()
				
				### Until the acknowledge is received, or the stop button is pressed, keep sending the message ###
				print(datetime.today().strftime('%H:%M:%S'))
				self.rfdThread.newCommandText.emit('\n' + datetime.today().strftime('%H:%M:%S'))		# Print out when the message began to send
				acknowledged = False
				while (not acknowledged):
					rfdSer.write(toSend)
					self.rfdThread.newCommandText.emit("Sent: " + toSend)		# Add the message to the browser every time it is sent
					line = rfdSer.readline()		# Read to look for the acknowledge, print out whatever you get for debugging purposes (so long as its not nothing)
					if(line != ''):
						print(line)
					if(line == identifier + '\n'):		# The acknowledge is the same as the identifier
						acknowledged = True
						print("Acknowledged at: " + datetime.today().strftime('%H:%M:%S'))
						self.rfdThread.newCommandText.emit("Acknowledged at: " + datetime.today().strftime('%H:%M:%S'))		# Print out the time of acknowledge to see how long it took to get the message through
						commandNewText = True
					if(commandInterrupt):		# If the stop button is pressed, interrupt the sending
						print("Interrupted")
						self.rfdThread.newCommandText.emit("Interrupted")
						commandNewText = True
						acknowledged = True
						
				### Listen for the response, and print it out ###
				final = ''
				done = False
				while(not done and not commandInterrupt):		# If the interrupt is used, break the loop
					final = str(rfdSer.readline())
					print(final)
					if (final.split(';')[0] == identifier):
						if final.find('!') != -1:
							done = True
				commandInterrupt = False
				self.rfdThread.newCommandText.emit(final)		# Add the message to the browser
				self.rfdThread.payloadUpdate.emit(final)		# Send it to the payload manager
				
				### Once the commands are finished sending and receiving, clean up ###
				rfdSer.close()		# Close the RFD serial port
				rfdCommandsOnline = False
				self.rfdCommandButton.setText("START")
				self.rfdCommandsOnlineLabel.setText("OFF")
				self.changeTextColor(self.rfdCommandsOnlineLabel,"red")
				
			else:		# If there's no RFD, print the message and get out
				print("No RFD Radio on this computer")
				return
		else:
			return
			
	def getPiRuntimeDataButtonPress(self):
		""" Check to see if the system is in a state where it can receive the pi Runtime Data """
		
		if(self.stillImageOnline):
			print("Still Image System cannot be Online")
			self.rfdReceiveBrowser.append("Still Image System cannot be Online")
			if(saveData):
				self.logData('RFD','newText'+','+'Still Image System cannot be Online')
			return
		if(rfdCommandsOnline or rfdListenOnline):
			print("RFD Commands cannot be Online")
			self.rfdReceiveBrowser.append("RFD Commands cannot be Online")
			if(saveData):
				self.logData('RFD','newText'+'RFD Commands cannot be Online')
			return

		if(not rfdAttached):
			print("No RFD Attached")
			self.rfdReceiveBrowser.append("No RFD Attached")
			if(saveData):
				self.logData('RFD','newText'+','+'No RFD Attached')
			
		rfdWorker = Worker(self.getPiRuntimeData)
		rfdWorker.moveToThread(self.rfdThread)
		rfdWorker.start.connect(rfdWorker.run)
		rfdWorker.start.emit("hello")
		self.rfdWorker = rfdWorker
			
	def getPiRuntimeData(self):
		""" Retrieve the runtime data from the Pi """
		
		if(rfdAttached):
			rfdSer = self.RFD.getDevice()
			
			### Send the pi 7 until the acknowledge is received, or until too much time has passed ###
			rfdSer.write('7')
			termtime = time.time() + 10
			timeCheck = time.time() + 1
			while (rfdSer.read() != 'A'):
				if(timeCheck < time.time()):
					print("Waiting for Acknowledge")
					self.rfdThread.newCommandText.emit("Waiting for Acknowledge")
					timeCheck = time.time() + 1
				rfdSer.write('7')
				if(termtime < time.time()):
					print("No Acknowldeg Received, Connection Error")
					self.rfdThread.newCommandText.emit("No Acknowledge Received, Connect Error")
					sys.stdout.flush()
					return
			
			### Receive piruntimedata.txt ###
			timecheck = time.time()
			try:
				f = open("piruntimedata.txt","w")
			except:
				print "Error opening file"
				self.rfdThread.newCommandText.emit("Error opening file")
				sys.stdout.flush()
				return
			timecheck = time.time()
			sys.stdin.flush()
			termtime = time.time()+60
			temp = rfdSer.readline()
			while((temp != "\r") & (temp != "") ):		# Write everything the radio is receiving to the file
				f.write(temp)
				temp = rfdSer.read()
				if (termtime < time.time()):
					print "Error receiving piruntimedata.txt"
					self.rfdThread.newCommandText.emit("Error receiving piruntimedata.txt")
					f.close()
					return
			f.close()
			rfdSer.close()
			
			print "piruntimedata.txt saved to local folder"
			self.rfdThread.newCommandText.emit("piruntimedata.txt saved")
			print "Receive Time =", (time.time() - timecheck)
			self.rfdThread.newCommandText.emit("Receive Time ="+str((time.time() - timecheck)))
			
			### Open piruntimedata.txt and print it into the command browser ###
			try:
				f = open('piruntimedata.txt','r')
				for line in f:
					print(line)
					self.rfdThread.newCommandText.emit(line)
				f.close()
			except:
				print("Error reading piruntimedata.txt")
				self.rfdThread.newCommandText.emit("Error reading piruntimedata.txt")
				
			sys.stdout.flush()
			return
					
	def updateRFDCommandsText(self,text):
		""" Update the RFD Commands text browser with the provided text """
		global saveData
		
		self.rfdReceiveBrowser.append(text)
		if saveData:		# Log data if data logging is on
			self.logData("RFD","newText"+','+text)
						
	def updatePayloads(self,received):
		""" 
		Updates the payloads by creating new ones when necessary, and adding messages 
		to the ones known. Updates the browsers in the payloads tabs as well
		"""
		global payloadList
		
		### Go through each payload in the payload list, and see if this message is from a known payload. Make a new payload if necessary ###
		knownPayload = False
		for each in payloadList:
			if each.getName() == str(received.split(';')[0]):			# If there is a payload with the identifier in the message, add it to the payload
				print("Here")
				each.addMessage(str(received.split(';')[1][:-2]))
				knownPayload = True
		
		if not knownPayload:
			if len(received.split(';')) == 2:												# If there is a new identifier, make a new payload and add the message to it
				print("Made new Payload: " + str(received.split(';')[0]))
				temp = self.tabs.currentIndex()
				self.tabs.setCurrentIndex(4)															# Change the current tab index to the payloads tab (to make sure the focus is right when making new layouts and placing them)
				self.createNewPayload(str(received.split(';')[0]),str(received.split(';')[1][:-2]))				# Make the new payload
				self.tabs.setCurrentIndex(temp)															# Switch back to the tab you were on before it was made
		
		### Update the text browsers and maps in the payloads tab for each payload ###
		for each in payloadList:
			for line in each.getNewMessages():
				each.getMessageBrowser().append(line.getTimestamp() + " || " + line.getMessage())
			for line in each.getNewGPSUpdates():
				each.getGPSBrowser().append(line.getTimestamp() + " || " + line.getMessage())
			if(each.hasMap() and each.inNewLocation()):
				each.updateMap()
		
	def changeTextColor(self, obj, color):
		""" Changes the color of a text label to either red or green """
		
		if color == "red":		# Makes the label red
			palette = QtGui.QPalette()
			brush = QtGui.QBrush(QtGui.QColor(243, 0 ,0))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Active, QtGui.QPalette.WindowText, brush)
			brush = QtGui.QBrush(QtGui.QColor(243, 0, 0))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Inactive, QtGui.QPalette.WindowText, brush)
			brush = QtGui.QBrush(QtGui.QColor(120, 120, 120))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Disabled, QtGui.QPalette.WindowText, brush)
			obj.setPalette(palette)
		if color == "green":		# Makes the label green
			palette = QtGui.QPalette()
			brush = QtGui.QBrush(QtGui.QColor(21, 255, 5))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Active, QtGui.QPalette.WindowText, brush)
			brush = QtGui.QBrush(QtGui.QColor(21, 255, 5))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Inactive, QtGui.QPalette.WindowText, brush)
			brush = QtGui.QBrush(QtGui.QColor(120, 120, 120))
			brush.setStyle(QtCore.Qt.SolidPattern)
			palette.setBrush(QtGui.QPalette.Disabled, QtGui.QPalette.WindowText, brush)
			obj.setPalette(palette)
			
	def createNewPayload(self,name,msg):
		""" Make a new payload, add the message received to it, and create the proper display windows in the payloads tab """
		global payloadList
		print("Create Payload")
		print(name,msg)
		
		if(len(payloadList) == 0):
			self.payloadTabs = QtGui.QTabWidget()
			self.payloadTabs.setStyleSheet('QTabBar { font-size: 18pt; font-family: MS Shell Dlg 2; }')
			self.payloadTabGridLayout.addWidget(self.payloadTabs)
		
		# Make the payload label
		newPayloadLabelName = "payloadLabel"+str(len(payloadList)+1)
		self.newPayloadLabel = QtGui.QLabel()
		self.newPayloadLabel.setText(name)
		# Make the payload Messages Label
		newPayloadMessagesLabelName = "payload"+str(len(payloadList)+1)+"MessagesLabel"
		self.newPayloadMessagesLabel = QtGui.QLabel()
		self.newPayloadMessagesLabel.setText("Messages")
		self.newPayloadMessagesLabel.setFont(QtGui.QFont('MS Shell Dlg 2',16))
		# Make the payload GPS Updates Label
		newPayloadGPSUpdatesLabelName = "payload"+str(len(payloadList)+1)+"GPSLabel"
		self.newPayloadGPSLabel = QtGui.QLabel()
		self.newPayloadGPSLabel.setText("GPS Updates")
		self.newPayloadGPSLabel.setFont(QtGui.QFont('MS Shell Dlg 2',16))
		# Make the Messages Browser
		newPayloadMessagesBrowserName = "payloadMessagesBrower"+str(len(payloadList)+1)
		self.newPayloadMessagesBrowser = QtGui.QTextBrowser()
		self.newPayloadMessagesBrowser.setSizePolicy(QtGui.QSizePolicy.Expanding,QtGui.QSizePolicy.Expanding)
		# Make the GPS Updates Browser
		newPayloadGPSBrowserName = "payloadGPSBrowser"+str(len(payloadList)+1)
		self.newPayloadGPSBrowser = QtGui.QTextBrowser()
		self.newPayloadGPSBrowser.setObjectName(newPayloadGPSBrowserName)
		self.newPayloadGPSBrowser.setSizePolicy(QtGui.QSizePolicy.Expanding,QtGui.QSizePolicy.Expanding)
		# Make the grid layout and add elements to it
		newGridName = "payloadGridLLayout"+str(len(payloadList)+1)
		self.newGrid = QtGui.QGridLayout()
		self.newGrid.setObjectName(newGridName)
		self.newGrid.addWidget(self.newPayloadMessagesLabel,0,0,1,1)
		self.newGrid.addWidget(self.newPayloadGPSLabel,0,1,1,1)
		self.newGrid.addWidget(self.newPayloadMessagesBrowser,1,0,1,1)
		
		if(internetAccess):			# Only make the map if you have internet access
			# Make the QWebView
			newPayloadWebViewName = 'payloadWebView'+str(len(payloadList)+1)
			self.newPayloadWebView = WebView()
			self.newPayloadWebView.setObjectName(newPayloadWebViewName)
			self.newPayloadWebView.setSizePolicy(QtGui.QSizePolicy.Ignored,QtGui.QSizePolicy.Expanding)
			# Make a Vertical Layout for the GPS Browser and Webview
			self.newPayloadVertical = QtGui.QVBoxLayout()
			self.newPayloadVertical.addWidget(self.newPayloadGPSBrowser)
			self.newPayloadVertical.addWidget(self.newPayloadWebView)
			self.newGrid.addLayout(self.newPayloadVertical,1,1,1,1)
			self.newPayloadWebView.setHtml(str(getMapHtml(currentBalloon.getLat(),currentBalloon.getLon())))
			
		else:
			self.newGrid.addWidget(self.newPayloadGPSBrowser,1,1,1,1)
		
		### Add the new objects to a new tab ###
		self.tempWidget = QWidget()
		self.tempWidget.setLayout(self.newGrid)
		self.payloadTabs.addTab(self.tempWidget,name)
		
		newPayload = Payload(name, self.newPayloadMessagesBrowser, self.newPayloadGPSBrowser)		# Create the new payload
		if(internetAccess):		# If there's internet, add the webview
			newPayload.addWebview(self.newPayloadWebView)
			
		newPayload.addMessage(msg)
		payloadList.append(newPayload)
		
	def searchComPorts(self):
		""" Sets the Connections based on the Com Ports in use """
		
		ardCheck = False
		serCheck = False
		rfdCheck = False
		aprsCheck = False
		ports = list(serial.tools.list_ports.comports())		# Gets a list of com ports on the computer (they come as ListPortInfo objects http://pyserial.readthedocs.io/en/latest/tools.html)
		
		### Go through each port, and determine if it matches a known device ###
		for each in ports:
			print(each)
			eachLst = str(each).split('-')
			if((eachLst[1].find("Arduino Uno") != -1) or (each.pid == 67)):		# The Arduino shows up as Arduino Uno
				arduinoCOM = eachLst[0].strip()
				self.arduinoCOM.setText(arduinoCOM)
				self.arduinoAttached.setChecked(True)
				self.getLocal.setChecked(True)
				self.bearingNorth.setChecked(False)
				ardCheck = True
				
			try:
				if(eachLst[1].find("Pololu Micro Maestro 6") and eachLst[2].find("Servo Controller Command Port") != -1):		# Mini Maestro shows up as Pololu Micro Maestro 6, but with 2 ports. We want the command port
					servoCOM = eachLst[0].strip()
					self.servoCOM.setText(servoCOM)
					self.servoAttached.setChecked(True)
					serCheck = True

			except:			# Because not every port has 2 '-' characters, the split function may not work, and you just need to pass through
				if((each.vid == 8187 and each.pid == 137) and each.location == None):
					servoCOM = eachLst[0].strip()
					self.servoCOM.setText(servoCOM)
					self.servoAttached.setChecked(True)
					serCheck = True
				
			if each.vid == 1027 and each.pid == 24577:			# RFD 900 has vid 1027 and pid 24577
				rfdCOM = each[0].strip()
				self.rfdCOM.setText(rfdCOM)
				self.rfdAttached.setChecked(True)
				rfdCheck = True
			
			if((eachLst[1].find("Prolific") != -1) or (each.vid == 1659 and each.pid == 8963)):			# The USB to Serial cable used with the APRS receiver has a Prolific chip, and identifies itself as Prolific USB-to-Serial Comm Port
				aprsCOM = eachLst[0].strip()
				self.aprsCOM.setText(aprsCOM)
				self.aprsAttached.setChecked(True)
				aprsCheck = True
				
		### After checking all of the ports, you can see if a device has been disconnected, and therefore should be removed from the connections ###
		if ardCheck == False:
			self.getLocal.setChecked(False)
			self.bearingNorth.setChecked(True)
			self.arduinoCOM.setText('')
			self.arduinoAttached.setChecked(False)
		if serCheck == False:
			self.servoCOM.setText('')
			self.servoAttached.setChecked(False)
		if rfdCheck == False:
			self.rfdCOM.setText('')
			self.rfdAttached.setChecked(False)
		if aprsCheck == False:
			self.aprsCOM.setText('')
			self.aprsAttached.setChecked(False)
			
	def disabledChecked(self):
		""" Makes sure that only the disabled autotrack option is checked """
		global autotrackBlock
		if(self.autoDisabled.isChecked()):
			autotrackBlock = True
			self.autoIridium.setChecked(False)
			self.autoAPRS.setChecked(False)
			self.autoRFD.setChecked(False)
		autotrackBlock = False

	def autotrackChecked(self):
		""" Makes sure that disabled isn't checked if there is an autotrack option checked """
		global autotrackBlock
		if(self.autoIridium.isChecked() or self.autoAPRS.isChecked() or self.autoRFD.isChecked()):
			if(not autotrackBlock):
				self.autoDisabled.setChecked(False)

	def calibrateIMU(self):
		""" Display the calibration values for the IMU in a visible window, and allow the user to select when the calibration is ready """
		global groundAlt,groundLat,groundLon,centerBear,antennaBear,centerBearSet, calibrationReady
		
		if arduinoAttached:
			if(not getLocal):
				self.createWarning('Need to select Get Local for Center Bearing')
				print("Need to select Get Local for Center Bearing")
				return

			try:
				s2 = self.arduino.getDevice()
			except:
				print("Error opening the Arduino serial port")
				return

			try:
				## Make the Display Window for the Calibration ###
				self.calibrationWindow = QWidget()
				self.calibrationWindow.setWindowTitle("IMU Calibration")
				self.vLayout = QtGui.QVBoxLayout()
				self.calBrowser = QtGui.QTextBrowser()
				self.calButton = QtGui.QPushButton()
				self.calLabel = QtGui.QLabel()
				self.calLabel.setText("Press Ready when you are done with the calibration")
				self.calButton.setText("Ready")
				self.calButton.clicked.connect(lambda: self.getCenterBearing(s2))
				self.vLayout.addWidget(self.calLabel)
				self.vLayout.addWidget(self.calBrowser)
				self.vLayout.addWidget(self.calButton)
				self.calibrationWindow.setLayout(self.vLayout)
				self.calibrationWindow.show()
			except:
				print("Error creating the calibration window")
				return
				
			temp_arduino = "0";
			calibrationReady = False
			while(not calibrationReady):		# Continuously loop until the IMU is calibrated to satisfaction
				temp_arduino = "0"
				s2.flushInput()		# Clear the buffer so it can get new info
				time.sleep(0.05)
				while(temp_arduino[0] != '~'):		# The arduino string is comma separated, and starts with ~
					temp_arduino = s2.readline()
					temp_arduino = temp_arduino.split(',')
					displayStr = 'System: ' + temp_arduino[7] + '; ' + 'Gyro: ' + temp_arduino[8] + '; ' + 'Accel: '+temp_arduino[9] + '; ' + 'Mag: '+temp_arduino[10]
					print(displayStr)
					self.calBrowser.append(displayStr)
				QCoreApplication.processEvents()
		else:
			self.createWarning('No Arduino Attached')
			print("No Arduino Attached")

	def getCenterBearing(self,s2):
		""" Acquire a center bearing and a GPS location from the calibration arduino """
		global groundAlt,groundLat,groundLon,centerBear,antennaBear,centerBearSet, calibrationReady

		self.calibrationWindow.deleteLater()
		self.calBrowser.deleteLater()
		self.calLabel.deleteLater()
		self.vLayout.deleteLater()
		self.calButton.deleteLater()
		calibrationReady = True
		temp_arduino = "0"
		s2.flushInput()					# Clear the buffer so it can read new info
		while(temp_arduino[0] != '~'):
			temp_arduino = s2.readline();
			temp_arduino = temp_arduino.split(',');
		tempLat = temp_arduino[1]		# Get ground station latitude
		tempLon = temp_arduino[2]		# Get ground station longitude
		tempAlt = temp_arduino[3]		# Get ground station altitude
		tempoffsetDegrees = "0.00"
		tempoffsetDegrees = temp_arduino[4]		# Get the offset for the center bearing
		tempLat = tempLat.split(".")
		groundLat = float(tempLat[0])+float(tempLat[1])/10000000 		# Convert the lat to decimal degrees as a float
		tempLon = tempLon.split(".")
		groundLon = float(tempLon[0])-float(tempLon[1])/10000000		# Convert the lon to decimal degrees as a float
		tempAlt = tempAlt.split(".")
		groundAlt = int(tempAlt[0])										# Get the altitude to the floor(foot)
		centerBear = float(tempoffsetDegrees)
		declination = float(geomag.declination(dlat = groundLat,dlon = groundLon, h = groundAlt))		# Determine the declination of the ground station location to adjust for the difference between magnetic and true north
		centerBear = (centerBear+declination)
		if centerBear > 360:
			centerBear = centerBear - 360
		elif centerBear < 0:
			centerBear = centerBear + 360
		s2.close()		# Close the arduino serial port
		print "Local Latitude: \t",groundLat
		print "Local Longitude:\t",groundLon
		print "Local Altitude: \t",groundAlt
		print "Offset Degrees: \t",centerBear
		print "Declination:	\t",declination
		print "Offset + Dec:   \t",(centerBear)
		print "-------------------------------------------------------"

		antennaBear = (centerBear)
		centerBearSet = True			# Lets the program know that the center bearing has been set before
		self.manualRefresh()
	
	def getIridium(self):
		""" Gets tracking information from the Iridium satellite modem by taking the information from the SQL database at Montana State University """
		global db_host, db_user, db_passwd, db_name
		global iridiumInterrupt

		prev = ''
		while(not iridiumInterrupt):
			### Connect to the SQL Database
			connected = False
			while(not connected):
				try:
					db_local = MySQLdb.connect(host=db_host,user=db_user,passwd=db_passwd,db=db_name)		# Connect to the database
					cursor = db_local.cursor()																# prepare a cursor object using cursor() method
					sql = "select gps_fltDate,gps_time,gps_lat,gps_long,gps_alt from gps where gps_IMEI = "+self.IMEI+" order by pri_key DESC"   
					cursor.execute(sql)
					connected = True
					if(iridiumInterrupt):
						cursor.close()
						db_local.close()
						connected = True
				except:
					print("Failed to connect to database, trying again")
					
			### Fetch a single row using fetchone() method. ###
			try:
				results = cursor.fetchone()
				if(results != prev):
					prev = results
					remoteTime = results[1].split(":")
					remoteHours = int(remoteTime[0])
					remoteMinutes = int(remoteTime[1])
					remoteSeconds = int(remoteTime[2])
					remoteTime = results[1]
					remoteSeconds = remoteSeconds + (60*remoteMinutes) + (3600*remoteHours)
					remoteLat = float(results[2])				   #http://stackoverflow.com/questions/379906/parse-string-to-float-or-int
					remoteLon = float(results[3])
					remoteAlt = float(results[4]) * 3.280839895  #(meters to feet conversion)

					### Create a new location object ###
					try:
						newLocation = BalloonUpdate(remoteTime,remoteSeconds,remoteLat,remoteLon,remoteAlt,"Iridium")
						if saveData:		# Log the balloon location
							self.logData("balloonLocation",newLocation.getTrackingMethod()+','+str(newLocation.getTime())+','+str(newLocation.getLat())+','+str(newLocation.getLon())+','+str(newLocation.getAlt())+','+str(newLocation.getBear())+','+str(newLocation.getEle())+','+str(newLocation.getLOS()))

					except:
						print("Error creating a new balloon location object from Iridium Data")

					### Update the graphing arrays with the new data ###
					try:
						self.updateGraphingArrays(remoteSeconds,newLocation)
					except:
						print("Error updating graphing arrays with Iridium Data")
						
					try:
						self.iridiumThread.newLocation.emit(newLocation)				# Notify the main GUI of the new location
					except:
						print("Error signaling the main thread for new Iridium Location")
			except:
				print("ERROR PARSING DATA FROM DATABASE: Cannot parse data or data may not exist, please double check your IMEI number")
		### Clean up ###
		try:
			cursor.close()
			db_local.close()
		except:
			print("Error closing database")
		iridiumStarted = False
		iridiumInterrupt = False
			
	def getRFD(self,data):
		""" Interprets a  GPS string received from the RFD into a balloon location update """
		global rfdTime, rfdLat, rfdLon, rfdAlt, rfdBear, rfdEle, rfdLOS, groundLat, groundLon
		
		### Interpret the balloon location list ###
		try:
			hours = data[0]		# Fix taken at this time
			minutes = data[1]		# Fix taken at this time
			seconds = data[2]		# Fix taken at this time
			lat = stringToFloat(data[3])		# Latitude in Degrees
			lon = stringToFloat(data[4])		# Longitude in Degrees
			alt = stringToFloat(data[5])		# Altitude in meters (sealevel)
			sat = stringToFloat(data[6][:-1])		# Number of Satellites
		except:
			print("Error interpretting RFD Data")

		### Do some calculations, get some values ###
		alt = alt*3.2808	# Convert Altitude to feet
		gpsTime = hours + ":" +  minutes + ":" + seconds.split(".")[0]
		rfdSeconds = stringToFloat(hours) * 3600 + stringToFloat(minutes)*60 + stringToFloat(seconds)

		### Create a new location object ###
		try:
			newLocation = BalloonUpdate(gpsTime,rfdSeconds,lat,lon,alt,"RFD")
			if saveData:		# Log the balloon location
				self.logData("balloonLocation",newLocation.getTrackingMethod()+','+str(newLocation.getTime())+','+str(newLocation.getLat())+','+str(newLocation.getLon())+','+str(newLocation.getAlt())+','+str(newLocation.getBear())+','+str(newLocation.getEle())+','+str(newLocation.getLOS()))
		except:
			print("Error creating a new balloon location object from RFD Data")

		### Update the graphing arrays with the new data ###
		try:
			self.updateGraphingArrays(rfdSeconds,newLocation)
		except:
			print("Error updating graphing arrays with Iridium Data")
			
		try:
			self.rfdThread.newLocation.emit(newLocation)				# Notify the main GUI of the new position
		except:
			print("Error signaling the main thread for new RFD Location")
		
	def getAPRS(self):
		""" Gets tracking information from the APRS receiver """
		global aprsCOM, aprsBaud, aprsTimeout, aprsInterrupt

		aprsSer = self.APRS.getDevice()

		while(not aprsInterrupt):
			### Read the APRS serial port, and parse the string appropriately 								###
			### Format: "Callsign">CQ,WIDE1-1,WIDE2-2:!"Lat"N/"Lon"EO000/000/A="Alt"RadBug,23C,982mb,001	###
			try:
				line = str(aprsSer.readline())
				print(line)
				idx = line.find(self.callsign)
				if(idx != -1):
					line = line[idx:]
					line = line[line.find("!")+1:line.find("RadBug")]
					line = line.split("/")
					
					### Get the individual values from the newly created list ###
					time = datetime.utcfromtimestamp(time.time()).strftime('%H:%M:%S')
					lat = line[0][0:-1]
					latDeg = stringToFloat(lat[0:2])
					latMin = stringToFloat(lat[2:])
					lon = line[1][0:line[1].find("W")]
					lonDeg = stringToFloat(lon[0:3])
					lonMin = stringToFloat(lon[3:])
					lat = latDeg + (latMin/60)
					lon = -lonDeg - (lonMin/60)
					alt = stringToFloat(line[3][2:])
					aprsSeconds = stringToFloat(time.split(':')[0]) * 3600 + stringToFloat(time.split(':')[1])*60 + stringToFloat(time.split(':')[2])
					
					### Create a new location object ###
					try:
						newLocation = BalloonUpdate(time,aprsSeconds,lat,lon,alt,"APRS")
						if saveData:		# Log the balloon location
							self.logData("balloonLocation",newLocation.getTrackingMethod()+','+str(newLocation.getTime())+','+str(newLocation.getLat())+','+str(newLocation.getLon())+','+str(newLocation.getAlt())+','+str(newLocation.getBear())+','+str(newLocation.getEle())+','+str(newLocation.getLOS()))
					except:
						print("Error creating a new balloon location object from APRS Data")

					### Update the graphing arrays with the new data ###
					try:
						self.updateGraphingArrays(aprsSeconds,newLocation)
					except:
						print("Error updating graphing arrays with APRS Data")
						
					try:
						self.aprsThread.newLocation.emit(newLocation)				# Notify the main GUI of the new location
					except:
						print("Error signaling the main thread for new APRS location")
			except:
				print("Error retrieving APRS Data")

		### Clean Up ###
		try:
			aprsSer.close()			# Close the APRS Serial Port
		except:
			print("Error closing APRS serial port")
		aprsStarted = False
		aprsInterrupt = False

	def updateGraphingArrays(self,seconds,location):
		if ((len(self.receivedTime) == 0)):
			self.receivedTime = np.append(self.receivedTime,seconds)
			self.receivedLon = np.append(self.receivedLon,location.getLon())
			self.receivedLat = np.append(self.receivedLat,location.getLat())
			self.receivedAlt = np.append(self.receivedAlt,location.getAlt())
			self.bearingLog = np.append(self.bearingLog,location.getBear())
			self.elevationLog = np.append(self.elevationLog,location.getEle())
			self.losLog = np.append(self.losLog,location.getLOS())
		elif(self.receivedTime[len(self.receivedTime) - 1] < seconds):
			self.receivedTime = np.append(self.receivedTime,seconds)
			self.receivedLon = np.append(self.receivedLon,location.getLon())
			self.receivedLat = np.append(self.receivedLat,location.getLat())
			self.receivedAlt = np.append(self.receivedAlt,location.getAlt())
			self.bearingLog = np.append(self.bearingLog,location.getBear())
			self.elevationLog = np.append(self.elevationLog,location.getEle())
			self.losLog = np.append(self.losLog,location.getLOS())

	def logData(self,type,msg):
		""" Logs the message in the correct file designated in the type argument """
		# try:
		if type == "RFD":
			f = open(self.rfdLog,'a')
		elif type == "stillImage":
			f = open(self.stillImageLog,'a')
		elif type == "balloonLocation":
			f = open(self.balloonLocationLog,'a')
		elif type == "pointing":
			f = open(self.pointingLog,'a')
		f.write(str(datetime.today().strftime("%m/%d/%Y %H:%M:%S"))+','+msg+'\n')
		f.close()
		# except:
			# print("Error logging data: "+type+','+msg)

	def setServoAccel(self):
		""" Sets the rate at which the servos accelerate """

		try:
			s = self.servos.getDevice()

			setAccel = [accelCommand,tiltChannel,tiltAccel,0]
			s.write(setAccel)
			setAccel = [accelCommand,panChannel,panAccel,0]
			s.write(setAccel)

			s.close()				# Close the servo serial port

		except:
			print("Error, could not set the servo acceleration, check com ports")
		
	def setServoSpeed(self):
		""" Sets the max speed at which the servos rotate """

		try:
			s = self.servos.getDevice()

			setSpeed = [speedCommand,tiltChannel,tiltSpeed,0]
			s.write(setSpeed)
			setSpeed = [speedCommand,panChannel,panSpeed,0]
			s.write(setSpeed)

			s.close()					# Close the servo serial port

		except:
			print("Error, could not set the servo speed, check com ports")

	def moveTiltServo(self,position):
		""" Takes a single argument, moves the tilt servo to the position specified by the argument """
		global antennaEle
		
		if servoAttached:
			try:
				s = self.servos.getDevice()
				
				### Move the tilt servo ###
				if(position < 71):		  #80 degrees upper limit
						moveTilt = [moveCommand,tiltChannel,chr(71)]
				elif(position > 123):	   #5 degrees lower limit
						moveTilt = [moveCommand,tiltChannel,chr(123)]
				else:
						moveTilt = [moveCommand,tiltChannel,chr(position)]
				s.write(moveTilt)
				print "\t\tMove Tilt: ", float(position)
				
				mGui.updateGround(0,5,((position - 127)*90/127.00))		 # Update the position the GUI says it's pointing to
				mGui.manualRefresh()		# Refresh the GUI to show the new values

				s.close()			# Close the servo serial port

			except:
				print("Error updating tilt servo position")
			
		else:
			print "Error: Settings indicate no servo connection"

	def movePanServo(self,position):
		""" Takes a single argument, moves the pan servo to the position specified by the argument """
		global antennaBear,previousPan

		if servoAttached:
			try:
				s = self.servos.getDevice()
				
				### Move the pan servo ###
				if previousPan > position:
					position += 1
				previousPan = position
				movePan = [moveCommand,panChannel,chr(255-position)]
				s.write(movePan)
				
				print "\t\tMove Pan: ", float(position)
				mGui.updateGround(0,4,centerBear +((position - 127)*90/127.00))			# Update the position the GUI says it's pointing to
				mGui.manualRefresh()			# Refesh the GUI to show the new values

				s.close()				# Close the servo serial port

			except:
				print("Error updating pan servo position")

		else:
			print "Error: Settings indicate no servo connection"

	def pointToMostRecentBalloon(self):
		""" Aims the tracker at the balloon, even if the antenna tracker is offline """
		
		print "Starting serial communication with",servoCOM
		if servoAttached:
			self.moveToTarget(currentBalloon.getBear(),currentBalloon.getEle())
			print "Move to Center Command Sent via", servoCOM
		else:
			print "Error: Settings set to no Servo Connection"

	def moveToCenterPos(self):
		""" Send servos to their center pos (should be horizontal and straight ahead if zeroed) """
		
		print "Starting serial communication with",servoCOM
		if servoAttached:
			self.moveTiltServo(127)
			self.movePanServo(127)
			print "Move to Center Command Sent via", servoCOM
		else:
			print "Error: Settings set to no Servo Connection"

	def panBothServos(self):
		""" Moves servos through range of motion tests """
		
		print "Starting serial communication with",servoCOM
		if servoAttached:
			for i in range(127,0,-1):
				self.moveTiltServo(i)
				self.movePanServo(i)
				time.sleep(0.05)
				i+=1
			time.sleep(1)

			for i in range(0,254,1):
				self.moveTiltServo(i)
				self.movePanServo(i)
				time.sleep(0.05)
				i+=1
			time.sleep(1)
			print "Motion Test Finished"
		else:
			print "Error: Settings set to no Servo Connection"

	def moveToTarget(self,bearing,elevation):
		""" Moves servos based on a bearing and elevation angle """
		global centerBear,antennaBear,antennaEle
		global tiltOffset, panOffset
		global saveData
		
		temp = 0
		# Uses the center bearing, and makes sure you don't do unnessessary spinning when you're close to 0/360
		if((bearing>180) and (centerBear == 0)):
				centerBear = 360
		elif (((centerBear - bearing) > 180) and (centerBear >= 270)):
				bearing = bearing + 360
		elif (((centerBear - bearing) > 180) and (centerBear <=180)):
				temp = centerBear
				centerBear = 360 + temp
		print ("\tBearing: %.0f" %(bearing+panOffset))
		print ("\tElevation Angle: %.0f"%(elevation+tiltOffset))
		# With new digital servos, can use map method as described here: http://arduino.cc/en/reference/map
		panTo = ((bearing - (centerBear - 168)) * (servo_max - servo_min) / ((centerBear + 168) - (centerBear - 168)) + servo_min) + (255*panOffset/360)		# Get the correct numerical value for the servo position by adjusting based on offset, max and min
		if panTo > 254: panTo = 254
		if panTo < 0: panTo = 0
		print "\tServo Degrees:"
		if servoAttached:
			self.movePanServo(math.trunc(panTo)) 
		#If Error in Antenna Mount i.e. put antenna on backwards fix with changing 0-elevation to elevation (must change tilt stops too
		tiltTo = (((0-elevation) - tilt_angle_min) * (servo_max - servo_min) / (tilt_angle_max - tilt_angle_min) + servo_min) + (255*(-tiltOffset)/360)		# Get the correct numerical value for the servo position by adjusting based on offset, max and min
		print(tiltTo)
		if tiltTo > 254: tiltTo = 254		# Don't go over the max
		if tiltTo < 0: tiltTo = 0			# Don't go under the min
		if servoAttached:		# Move the servos to the new locations if they're attacheed
			self.moveTiltServo(math.trunc(tiltTo))
		if (temp!= 0):
				centerBear = temp
			
		# Write the new pointing location to the log file
		self.logData("pointing",str(bearing)+','+str(elevation))
		# Update the globals
		antennaBear = bearing
		antennaEle = elevation

def getMapHtml(lat,lon):
	""" Generates an HTML and JavaScript code segment using Google Maps API to plot the lat and lon on a map """
	
	maphtml = """
	<!DOCTYPE html>
	<html>
	  <head>
		<meta name="viewport" content="initial-scale=1.0, user-scalable=no">
		<meta charset="utf-8">
		<title>Circles</title>
		<style>
		  html, body {
			height: 100%;
			margin: 0;
			padding: 0;
		  }
		  #map {
			height: 100%;
		  }
		</style>
	  </head>
	  <body>
		<div id="map"></div>
		<script>
		  // This example creates circles on the map

		  // First, create an object containing LatLng and radius for each item.
		  var balloon = {
			payload: {
			  center: {lat: """ + str(lat) + """, lng: """ + str(lon)+"""},
			  rad: 3000
			}
		  };

			function initMap() {
			  var myLatLng = {lat: """+str(lat)+""", lng: """+str(lon)+"""};

			  var map = new google.maps.Map(document.getElementById('map'), {
			    zoom: 8,
			    center: myLatLng
			  });

			  var marker = new google.maps.Marker({
			    position: myLatLng,
			    map: map,
			    title: 'Hello World!'
			  });
			}
		  
		</script>
		<script async defer
		src="https://maps.googleapis.com/maps/api/js?key="""+str(googleMapsApiKey)+"""&callback=initMap">
		</script>
	  </body>
	</html>
	"""
	return maphtml
	
	
def stringToFloat(s):
	""" Converts a string to a float, 0 = '' """
	
	if(s == ''):
		return float(0)
	else:
		return float(s)
	
		
def bearing(trackerLat, trackerLon, remoteLat, remoteLon):
	""" great circle bearing, see: http://www.movable-type.co.uk/scripts/latlong.html  """
	
	dLat = math.radians(remoteLat-trackerLat)	   # delta latitude in radians
	dLon = math.radians(remoteLon-trackerLon)	   # delta longitude in radians
	
	y = math.sin(dLon)*math.cos(math.radians(remoteLat))
	x = math.cos(math.radians(trackerLat))*math.sin(math.radians(remoteLat))-math.sin(math.radians(trackerLat))*math.cos(math.radians(remoteLat))*math.cos(dLat)
	tempBearing = math.degrees(math.atan2(y,x))	 # returns the bearing from true north
	while(tempBearing < 0):		# Makes sure the bearing is between 0 and 360
		tempBearing += 360
	while(tempBearing > 360):
		tempBearing -= 360
	return tempBearing
		
def elevationAngle(skyAlt,trackerAlt, distance):
	""" elevation angle from ground distance and altitudes """
	
	return math.degrees(math.atan2(skyAlt-trackerAlt,distance))
		
def haversine(trackerLat, trackerLon, remoteLat, remoteLon):
	""" haversine formula, see: http://www.movable-type.co.uk/scripts/latlong.html """
	
	R = 6371		# radius of earth in Km
	dLat = math.radians(remoteLat-trackerLat)	   # delta latitude in radians
	dLon = math.radians(remoteLon-trackerLon)	   # delta longitude in radians
	
	a = math.sin(dLat/2)*math.sin(dLat/2)+math.cos(math.radians(trackerLat))*math.cos(math.radians(remoteLat))*math.sin(dLon/2)*math.sin(dLon/2)
	c = 2*math.atan2(math.sqrt(a),math.sqrt(1-a))
	
	d = R*c
	
	return d*3280.839895 # multiply distance in Km by 3280 for feet

def losDistance(alt,trackerAlt,distance):
	""" The line of sight distance based on ground distance and altitude """

	return math.sqrt(math.pow(distance/3.2808,2) + math.pow((alt-trackerAlt)/3.2808,2))/1000

def image_to_b64(path):
	""" Converts an image to a base64 encoded String (ASCII characters) """
	
	with open(path,"rb") as imageFile:
		return base64.b64encode(imageFile.read())

def b64_to_image(data,savepath):
	""" Converts a base64 encoded string of ASCII characters back to an image, the save path dictates image format """
	fl = open(savepath, "wb")
	fl.write(data.decode('base64'))
	fl.close()
	
def gen_checksum(data):
	""" Generates a 32 character hash up to 10000 char length String(for checksum). If string is too long I've notice length irregularities in checksum """
	return hashlib.md5(data).hexdigest()
	
if __name__ == "__main__":
	app=QtGui.QApplication.instance()		# checks if QApplication already exists 
	if not app:								# create QApplication if it doesnt exist 
		app = QtGui.QApplication(sys.argv)
		
	# Let's .jpg images be shown by adding the imageformats folder to to the path (http://www.qtcentre.org/threads/49119-JPG-not-working-when-calling-setPixmap()-on-QLabel)
	path = r"C:\Users\Ground Station\Anaconda2\Lib\site-packages\PySide\plugins"
	app.addLibraryPath(path)
	
	mGui = MainWindow()						# Launch the main window
	mGui.showMaximized()					# Shows the main window maximized
	sys.stdout = Unbuffered(sys.stdout)		# Sets up an unbuffered stream
	app.exec_()								# Starts the application
	
	### At the close of the program, write each payload's information to a file ###
	for each in payloadList:
		payloadInstance = "Logs/"+each.getName() + '-'+str(datetime.today().strftime("%m-%d-%Y %H-%M-%S")+'.txt')
		f = open(payloadInstance,'w')
		for one in each.getMessages():
			f.write('Message' + ','+  str(one.getTimestamp())+','+str(one.getMessage()) + '\n')
		for one in each.getGPSUpdates():
			f.write("GPS" + ','+  str(one.getTimestamp())+','+str(one.getMessage()) + '\n')
		f.close()
		
else:
	print "Error Booting Gui"
	while(1):
		pass


