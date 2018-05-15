--[[
    ----------------------------------------------------------------------------
    App using JLog2.6 Sensor Data from motor control for helicopter usage
   
        Based on a work, modified by Rene S.,
        from A. Fromm who in turn copied part of the code
        from github.com RC-Thoughts/Lua_LiPo_Watcher
        MIT-license by Tero @ RC-Thoughts.com 2017
    
    ----------------------------------------------------------------------------
    MIT License
   
    Hiermit wird unentgeltlich jeder Person, die eine Kopie der Software und der
    zugehörigen Dokumentationen (die "Software") erhält, die Erlaubnis erteilt,
    sie uneingeschränkt zu nutzen, inklusive und ohne Ausnahme mit dem Recht, sie
    zu verwenden, zu kopieren, zu verändern, zusammenzufügen, zu veröffentlichen,
    zu verbreiten, zu unterlizenzieren und/oder zu verkaufen, und Personen, denen
    diese Software überlassen wird, diese Rechte zu verschaffen, unter den
    folgenden Bedingungen: 
    Der obige Urheberrechtsvermerk und dieser Erlaubnisvermerk sind in allen Kopien
    oder Teilkopien der Software beizulegen. 
    DIE SOFTWARE WIRD OHNE JEDE AUSDRÜCKLICHE ODER IMPLIZIERTE GARANTIE BEREITGESTELLT,
    EINSCHLIEßLICH DER GARANTIE ZUR BENUTZUNG FÜR DEN VORGESEHENEN ODER EINEM
    BESTIMMTEN ZWECK SOWIE JEGLICHER RECHTSVERLETZUNG, JEDOCH NICHT DARAUF BESCHRÄNKT.
    IN KEINEM FALL SIND DIE AUTOREN ODER COPYRIGHTINHABER FÜR JEGLICHEN SCHADEN ODER
    SONSTIGE ANSPRÜCHE HAFTBAR ZU MACHEN, OB INFOLGE DER ERFÜLLUNG EINES VERTRAGES,
    EINES DELIKTES ODER ANDERS IM ZUSAMMENHANG MIT DER SOFTWARE ODER SONSTIGER
    VERWENDUNG DER SOFTWARE ENTSTANDEN. 
        ----------------------------------------------------------------------------

   Tero Salminen History (reverse order): 
   
   2017-10-28  Tero Salminen  <tero@rc-thoughts.com>
    * v.1.2 Changed the way calculation is done, changed to 
            max. voltage tracking, tested in DS-16

   2017-10-22  Tero Salminen  <tero@rc-thoughts.com>
    * v.1.1 Added possibility to adjust averaging value

   2017-10-22  Tero Salminen  <tero@rc-thoughts.com>
    * v.1.0 First release
   
    A. Fromm History:    
   	Versionshistory:
	16.01.2018	V1.06	released
	16.01.2018	V1.07	Unterscheidung Unilog2/Unisens
	18.01.2018	V1.08	Anzeige Nachkommastellen bei Stromanzeige 0-99.99A 2 Stellen

   Rene S. History:
   no History
   
   nichtgedacht Version History:
   V2.0 initial release
   V2.1 display max values better reading. Added display for Gyro setting
    
--]]

--[[
Jlog2.6 Telemetry Parameters (Number is Sensor Parameter, quoted Text is Parameter Label):
                                                                                                                                          
Basis                                                                                                                                     
1 “U battery”   nn.n    V   (Akkuspannung)
2 “I motor”     nnn.n   A   (Motorstrom)
3 “RPM uni”     nnnn    rpm (Rotordrehzahl)
4 “mAh”         nnnnn   mAh (verbrauchte Kapazität)
5 “U bec”       n.n     V   (BEC-Ausgangsspannung)
6 “I bec”       nn.n    A   (BEC-Ausgangsstrom)
7 “Throttle”    nnn     %   (Gas 0..100%)
8 “PWM”         nnn     %   (Stelleraussteuerung 0..100%)
9 “Temp         nnn     °C  (Temperatur der Leistungs-FETs (Endstufe), bisher “TempPA” genannt)
   
+
   
Configuration 0 setup by JLC5 (Standard):
10 “extTemp1″   [-]nn.n     °C (JLog-eigener (Steller-externer) Temperatursensor 1 (1/5))
11 “extTemp2″   [-]nn.n     °C (JLog-eigener (Steller-externer) Temperatursensor 2 (2/5))
12 “extRPM”     nnnnn       rpm (JLog-eigener (Steller-externer) Drehzahlsensor)
13 “Speed”      nnn         km/h (JLog-eigener Sensor, Prandtl-Sonde (Staurohr) SM#2560)
14 “MaxSpd”     nnn         km/h (Maximalgeschwindigkeit)
15 “RPM mot”    nnnnn       rpm (Motordrehzahl)

or Configuration 1 (selected config) setup by JLC5 (Min/Max-Werte):
10 “RPM mot”    nnnnn   rpm (Motordrehzahl)
11 “Ubat Min”   nn.n    V   (Akkuminimalspannung)
12 “Ubec Min”   n.n     V   (BEC-Minimalspannung)
13 “Imot Max”   nnn.n   A   (Motormaximalstrom)
14 “Ibec Max”   nn.n    A   (BEC-Maximalstrom)
15 “Power Max”  nnnnn   W   (Maximalleistung)
--]]


collectgarbage()
--------------------------------------------------------------------------------
local initial_voltage_measured = false
local initial_capacity_percent_used = 0
local initial_cell_voltage, cell_count
local model, owner = " ", " "
local trans, anCapaSw, anVoltSw, anCapaGo, anVoltGo
local sensorId, capacity_alarm_thresh
local battery_voltage, battery_voltage_average, motor_current, rotor_rpm, used_capacity, rx_voltage = 0.0, 0.0, 0.0, 0, 0, 0.00
local bec_current, pwm_percent, fet_temp = 0, 0, 0
local capacity, remaining_capacity_percent, minpwm, maxpwm = 0, 100, 0, 0
local minrpm, maxrpm, mincur, maxcur = 999, 0, 99.9, 0
local minvtg, maxvtg, mintmp, maxtmp = 99, 0, 99, 0
local fTime
local time, lastTime, newTime = 0, 0, 0
local std, min, sec = 0, 0, 0
local minrxv, maxrxv, minrxa, maxrxa = 9.9, 0.0, 9.9, 0.0
local next_capacity_announcement, next_voltage_announcement, tTime = 0, 0, 0
local voltage_alarm_voice, capacity_alarm_voice
local voltage_alarm_thresh, voltage_alarm_dec_thresh
local next_capacity_alarm, next_voltage_alarm = 0, 0
local last_averaging_time = 0
local voltages_list = {}
--local rx_percent = 0 -- signal quality not used
local rx_a1, rx_a2 = 0, 0
--local volume_playback, volume
local gyro_output, gyChannel
local gyro_channel = 0
local output_list = { "O1", "O2", "O3", "O4", "O5", "O6", "O7", "O8", "O9", "O10", "O11", "O12",
		              "O13", "O14", "O15", "O16", "O17", "O18", "O19", "O20", "O21", "O22", "O23", "O24" }


-- maps cell voltages to remainig capacity
local percentList	=	{{3,0},{3.093,1},{3.196,2},{3.301,3},{3.401,4},{3.477,5},{3.544,6},{3.601,7},{3.637,8},{3.664,9},
						{3.679,10},{3.683,11},{3.689,12},{3.692,13},{3.705,14},{3.71,15},{3.713,16},{3.715,17},{3.72,18},
						{3.731,19},{3.735,20},{3.744,21},{3.753,22},{3.756,23},{3.758,24},{3.762,25},{3.767,26},{3.774,27},
						{3.78,28},{3.783,29},{3.786,30},{3.789,31},{3.794,32},{3.797,33},{3.8,34},{3.802,35},{3.805,36},
						{3.808,37},{3.811,38},{3.815,39},{3.818,40},{3.822,41},{3.825,42},{3.829,43},{3.833,44},{3.836,45},
						{3.84,46},{3.843,47},{3.847,48},{3.85,49},{3.854,50},{3.857,51},{3.86,52},{3.863,53},{3.866,54},
						{3.87,55},{3.874,56},{3.879,57},{3.888,58},{3.893,59},{3.897,60},{3.902,61},{3.906,62},{3.911,63},
						{3.918,64},{3.923,65},{3.928,66},{3.939,67},{3.943,68},{3.949,69},{3.955,70},{3.961,71},{3.968,72},
						{3.974,73},{3.981,74},{3.987,75},{3.994,76},{4.001,77},{4.007,78},{4.014,79},{4.021,80},{4.029,81},
						{4.036,82},{4.044,83},{4.052,84},{4.062,85},{4.074,86},{4.085,87},{4.095,88},{4.105,89},{4.111,90},
						{4.116,91},{4.12,92},{4.125,93},{4.129,94},{4.135,95},{4.145,96},{4.176,97},{4.179,98},{4.193,99},
						{4.2,100}}

--[[
    Alternative List to be interpolated
{3.000, 0},           
{3.380, 5},
{3.580, 10},
{3.715, 15},
{3.747, 20},
{3.769, 25},
{3.791, 30},
{3.802, 35},
{3.812, 40},
{3.826, 45},
{3.839, 50},
{3.861, 55},
{3.883, 60},
{3.910, 65},
{3.936, 70},
{3.986, 75},
{3.999, 80},
{4.042, 85},
{4.085, 90},
{4.142, 95},
{4.170, 97},
{4.200, 100}    
--]]    
                   
--------------------------------------------------------------------------------
-- Read translations
local function setLanguage()
	local lng=system.getLocale()
	local file = io.readall("Apps/Lang/JLog26.jsn")
	local obj = json.decode(file)
	if(obj) then
		trans = obj[lng] or obj[obj.default]
	end
end
--------------------------------------------------------------------------------
-- Draw Battery and percentage display
local function drawBattery()
	
	-- Battery
	lcd.drawFilledRectangle(148, 48, 24, 7)	-- Top of Battery
	lcd.drawRectangle(134, 55, 52, 80)
	-- Level of Battery
	chgY = (135 - (remaining_capacity_percent * 0.8))
	chgH = (remaining_capacity_percent * 0.8)
	
	lcd.drawFilledRectangle(135, chgY, 50, chgH)
			
	-- Percentage Display
	if( remaining_capacity_percent > capacity_alarm_thresh ) then	
		lcd.drawRectangle(115, 2, 90, 43, 10)
		lcd.drawRectangle(114, 1, 92, 45, 11)
		lcd.drawText(160 - (lcd.getTextWidth(FONT_MAXI, string.format("%.0f%%",remaining_capacity_percent)) / 2),4, string.format("%.0f%%",
							remaining_capacity_percent),FONT_MAXI)
	else
		if( system.getTime() % 2 == 0 ) then -- blink every second
			lcd.drawRectangle(115, 2, 90, 43, 10)
			lcd.drawRectangle(114, 1, 92, 45, 11)
			lcd.drawText(160 - (lcd.getTextWidth(FONT_MAXI, string.format("%.0f%%",remaining_capacity_percent)) / 2),4, string.format("%.0f%%",
								remaining_capacity_percent),FONT_MAXI)
		end
	end
		
	collectgarbage()
end
--------------------------------------------------------------------------------
-- Draw left top box
local function drawLetopbox()    -- Flightpack Voltage
	-- draw fixed Text
	lcd.drawText(57 - (lcd.getTextWidth(FONT_MINI,trans.mainbat) / 2),1,trans.mainbat,FONT_MINI)
	lcd.drawText(82, 20, "V", FONT_MINI)
	lcd.drawText(6, 32, "Min/Max:", FONT_MINI)
		
	-- draw Values
	lcd.drawText(80 - lcd.getTextWidth(FONT_BIG, string.format("%.1f", battery_voltage_average)),13, string.format("%.1f",
	battery_voltage_average), FONT_BIG)
	lcd.drawText(60, 32, string.format("%.1f - %.1f", minvtg, maxvtg), FONT_MINI)
end
--------------------------------------------------------------------------------
-- Draw left middle box
local function drawLemidbox()	-- Rotor Speed
	-- draw fixed Text
	lcd.drawText(50 - (lcd.getTextWidth(FONT_MINI,trans.rotspeed) / 2),50,trans.rotspeed,FONT_MINI)
	lcd.drawText(82, 81, "U/min", FONT_MINI)
	lcd.drawText(6, 97, "Min/Max:", FONT_MINI)
		
	-- draw Values
	lcd.drawText(80 - lcd.getTextWidth(FONT_MAXI,string.format("%.0f",rotor_rpm)),61,string.format("%.0f",rotor_rpm),FONT_MAXI)
       lcd.drawText(60,97, string.format("%.0f - %.0f", minrpm, maxrpm), FONT_MINI)
end
--------------------------------------------------------------------------------
-- Draw left bottom box
local function drawLebotbox()	-- BEC Voltage
	-- draw fixed Text
	lcd.drawText(6, 116, "I", FONT_BIG)
	lcd.drawText(14, 124, "Motor:", FONT_MINI)
	lcd.drawText(110, 124, "A", FONT_MINI)
        
	-- draw current 
	lcd.drawText(105 - lcd.getTextWidth(FONT_BIG, string.format("%.1f",motor_current)),116, string.format("%.1f",motor_current),FONT_BIG)
        
	-- separator
	lcd.drawFilledRectangle(4, 142, 116, 2)
        
	-- draw fixed Text
	lcd.drawText(6, 148, "URx", FONT_MINI)
	lcd.drawText(70, 148, "A", FONT_MINI)
	
	-- draw RX Values
	lcd.drawText(118 - lcd.getTextWidth(FONT_MINI, string.format("%d   %d",rx_a1, rx_a2)),148, string.format("%d   %d",rx_a1, rx_a2),FONT_MINI)
	--lcd.drawText(120 - lcd.getTextWidth(FONT_MINI, string.format("%.0f %%",rx_percent)),148, string.format("%.0f %%",rx_percent),FONT_MINI)
	lcd.drawText(60 - lcd.getTextWidth(FONT_MINI, string.format("%.2fV",rx_voltage)),148, string.format("%.2fV",rx_voltage),FONT_MINI) 
end
--------------------------------------------------------------------------------
-- Draw right top box
local function drawRitopbox()	-- Flight Time
	-- draw fixed Text
	lcd.drawText(265 - (lcd.getTextWidth(FONT_MINI, trans.ftime)/2), 1, trans.ftime, FONT_MINI)
	lcd.drawText(251 - (lcd.getTextWidth(FONT_MINI, trans.date)), 32, trans.date, FONT_MINI)
	
	-- draw Values
	lcd.drawText(255 - (lcd.getTextWidth(FONT_BIG, string.format("%0d:%02d:%02d", std, min, sec)) / 2), 13, string.format("%0d:%02d:%02d",
						std, min, sec), FONT_BIG)
	lcd.drawText(255, 32, string.format("%02d.%02d.%02d", today.day, today.mon, today.year), FONT_MINI)
end
--------------------------------------------------------------------------------
-- Draw right middle box
local function drawRimidbox()	-- Used Capacity
    
	local total_used_capacity = math.ceil( used_capacity + (initial_capacity_percent_used * capacity) / 100 )
	
	-- draw fixed Text
	lcd.drawText(262 - (lcd.getTextWidth(FONT_MINI,trans.usedCapa) / 2),50,trans.usedCapa,FONT_MINI)
	lcd.drawText(285, 81, "mAh", FONT_MINI)
	lcd.drawText(205, 97, trans.capacity, FONT_MINI)
		
	-- draw Values
	lcd.drawText(282 - lcd.getTextWidth(FONT_MAXI, string.format("%.0f",total_used_capacity)),61, string.format("%.0f",
				total_used_capacity), FONT_MAXI)
	lcd.drawText(258,97, string.format("%s mAh", capacity),FONT_MINI)
end
--------------------------------------------------------------------------------
-- Draw right bottom box
local function drawRibotbox()	-- Some Max Values

	-- draw fixed Text
	lcd.drawText(205, 113, "MaxIBEC", FONT_MINI)
	lcd.drawText(205, 125, "MaxIMot", FONT_MINI)
	lcd.drawText(205, 137, "MaxPWM", FONT_MINI)
	lcd.drawText(205, 149, "MaxTFETs", FONT_MINI)
	
	lcd.drawText(302,113,"A",FONT_MINI)
	lcd.drawText(302,125,"A",FONT_MINI)
	lcd.drawText(302,137,"%",FONT_MINI)
	lcd.drawText(302,149,"°C",FONT_MINI)
	
	-- draw Max Values  
	lcd.drawText(295 - lcd.getTextWidth(FONT_MINI, string.format("%.1f",maxrxa)),113, string.format("%.1f",maxrxa),FONT_MINI)
	lcd.drawText(295 - lcd.getTextWidth(FONT_MINI, string.format("%.1f",maxcur)),125, string.format("%.1f",maxcur),FONT_MINI)
	lcd.drawText(295 - lcd.getTextWidth(FONT_MINI, string.format("%.0f",maxpwm)),137, string.format("%.0f",maxpwm),FONT_MINI)
	lcd.drawText(295 - lcd.getTextWidth(FONT_MINI, string.format("%.0f",maxtmp)),149, string.format("%.0f",maxtmp),FONT_MINI)
end

local function drawMibotbox()
	
	local gyro_percent = (gyro_channel * 100 + 39) * 0.6060 + 40
	
	if (gyro_percent < 40) then gyro_percent = 40 end
	if (gyro_percent > 120) then gyro_percent = 120 end
	
	-- draw fixed Text
	lcd.drawText(136,145,"GY",FONT_MINI)
	-- draw Max Values
	lcd.drawText(184 - lcd.getTextWidth(FONT_BIG, string.format("%.0f", gyro_percent)), 138, string.format("%.0f",
				 gyro_percent), FONT_BIG)
end	

--------------------------------------------------------------------------------
-- Telemetriefenster Page1
local function Page1(width, height)

	drawBattery()
	drawLetopbox()
	drawLemidbox()
	drawLebotbox()
	drawRitopbox()
	drawRimidbox()
	drawRibotbox()
	drawMibotbox()
	
	-- draw horizontal lines
	lcd.drawFilledRectangle(4, 47, 104, 2)     --lo
	lcd.drawFilledRectangle(4, 111, 116, 2)    --lu
	lcd.drawFilledRectangle(212, 47, 104, 2)   --ro
	lcd.drawFilledRectangle(200, 111, 116, 2)  --ru
	lcd.drawFilledRectangle(4, 142, 116, 2)
end
--------------------------------------------------------------------------------

local function capacityChanged(value)
	capacity = value
	system.pSave("capacity", capacity)
end

local function cell_countChanged(value)
	cell_count = value
	system.pSave("cell_count", cell_count)
end

local function capacity_alarm_threshChanged(value)
	capacity_alarm_thresh = value
	system.pSave("capacity_alarm_thresh", capacity_alarm_thresh)
end

local function capacity_alarm_voiceChanged(value)
	capacity_alarm_voice = value
	system.pSave("capacity_alarm_voice", capacity_alarm_voice)
end

local function timeSwChanged(value)
	timeSw = value
	system.pSave("timeSw", timeSw)
end

local function resSwChanged(value)
	resSw = value
	system.pSave("resSw", resSw)
end

local function anCapaSwChanged(value)
	anCapaSw = value
	system.pSave("anCapaSw", anCapaSw)
end

local function anVoltSwChanged(value)
	anVoltSw = value
	system.pSave("anVoltSw", anVoltSw)
end

local function voltage_alarm_threshChanged(value)
	voltage_alarm_thresh=value
	voltage_alarm_dec_thresh = voltage_alarm_thresh / 10
	system.pSave("voltage_alarm_thresh", voltage_alarm_thresh)
end

local function voltage_alarm_voiceChanged(value)
	voltage_alarm_voice=value
	system.pSave("voltage_alarm_voice", voltage_alarm_voice)
end

local function gyChChanged(value)
	gyChannel = value
	gyro_output = output_list[gyChannel]
	
	system.pSave("gyChannel", gyChannel)
end

--------------------------------------------------------------------------------
local function setupForm(formID)
    
	local available = system.getSensors()
	for index,sensor in ipairs(available) do 
		if(sensor.param == 0) then
			if ( sensor.label == "JLog2.6" ) then
				sensorId = sensor.id
				system.pSave("sensorId", sensor.id)
				break
			end
		end
	end
	
	form.setTitle(trans.title)
				
	form.addSpacer(318,7)
	
	form.addRow(1)
	form.addLabel({label=trans.label1,font=FONT_BOLD})
	
	form.addRow(2)
	form.addLabel({label=trans.anCapaSw, width=210})
	form.addInputbox(anCapaSw,true,anCapaSwChanged)

	form.addRow(2)
	form.addLabel({label=trans.anVoltSw, width=210})
	form.addInputbox(anVoltSw,true,anVoltSwChanged)
        
	form.addSpacer(318,7)

	form.addRow(1)
	form.addLabel({label=trans.label3,font=FONT_BOLD})

	form.addRow(2)
	form.addLabel({label=trans.voltAlarmVoice, width=210})
	form.addAudioFilebox(voltage_alarm_voice,voltage_alarm_voiceChanged)
        
	form.addRow(2)
	form.addLabel({label=trans.capaAlarmVoice, width=210})
	form.addAudioFilebox(capacity_alarm_voice, capacity_alarm_voiceChanged)
	
	form.addSpacer(318,7)
	
	form.addRow(1)
	form.addLabel({label=trans.label2,font=FONT_BOLD})
	
	form.addRow(2)
	form.addLabel({label=trans.capacitymAh, width=210})
	form.addIntbox(capacity, 0, 32767, 0, 0, 10, capacityChanged)
	
	form.addRow(2)
	form.addLabel({label=trans.cellcnt, width=210})
	form.addIntbox(cell_count, 1, 12, 1, 0, 1, cell_countChanged)
	
	form.addRow(2)
	form.addLabel({label=trans.capaAlarmThresh, width=210})
	form.addIntbox(capacity_alarm_thresh, 0, 100, 0, 0, 1, capacity_alarm_threshChanged)
    
	form.addRow(2)
	form.addLabel({label=trans.voltAlarmThresh, width=210})
	form.addIntbox(voltage_alarm_thresh,0,1000,0,1,1,voltage_alarm_threshChanged)
	
	form.addSpacer(318,7)
	
	form.addRow(1)
	form.addLabel({label=trans.label4,font=FONT_BOLD})
	
	form.addRow(2)
	form.addLabel({label=trans.timeSw, width=210})
	form.addInputbox(timeSw,true,timeSwChanged)
	
	form.addRow(2)
	form.addLabel({label=trans.resSw, width=210})
	form.addInputbox(resSw,true,resSwChanged)
	
	form.addSpacer(318,7)
	
	form.addRow(1)
	form.addLabel({label=trans.label5,font=FONT_BOLD})
	
	form.addRow(2)
	form.addLabel({label=trans.channel, width=210})
	form.addIntbox(gyChannel,1,16,6,0,1,gyChChanged)
	
	form.addSpacer(318,7)

	form.addRow(1)
	form.addLabel({label="JLog2.6-Heli " .. Version .. " ", font=FONT_MINI, alignRight=true})
    
	collectgarbage()
end
--------------------------------------------------------------------------------
-- Fligt time
local function FlightTime()
	newTime = system.getTimeCounter()
	ltimeSw = system.getInputsVal(timeSw)
	resetSw = system.getInputsVal(resSw)
	
	-- if (ltimeSw ~= 1 and resetSw == 1) then time = 0 end
	-- to be in sync with a timer, do not use CLR key 
	if (resetSw == 1) then time = 0 end
        
	if newTime >= (lastTime + 1000) then  -- one second
		lastTime = newTime
		if (ltimeSw == 1) then 
			time = time + 1
		end
	end
	
	std = math.floor(time / 3600)
	min = math.floor(time / 60) - std * 60
	sec = time - min * 60
	
	collectgarbage()
end
    
-- Count percentage from cell voltage
local function get_capacity_percent_used()
	result=0
	if(initial_cell_voltage > 4.2 or initial_cell_voltage < 3.00)then
		if(initial_cell_voltage > 4.2)then
			result=0
		end
		if(initial_cell_voltage < 3.00)then
			result=100
		end
		else
		for i,v in ipairs(percentList) do
			if ( v[1] >= initial_cell_voltage ) then
				result =  100 - v[2]
				break
			end
		end
	end
	collectgarbage()
	return result
end

--[[
function moving_average(number)
	local list = {}
	function sum(a, ...)
		if a then return a+sum(...) else return 0 end
	end
	function average_list(value)
		if #list == number then table.remove(list, 1) end -- if list contains numer elements shift 1 position to left  
		list[#list + 1] = value                           -- push to end of list
		return sum(table.unpack(list)) / #list                  -- return current average
	end
	collectgarbage()
	return average_list -- return the averaging function in order to instanciate it, keep upvalues number and list within the instances
end
--]]   


function average(value) -- smaller averaging implementation bcs just used for averaging voltage
    
	local sum_voltages = 0
	local voltage
	local i
	
	if ( #voltages_list == 5 ) then
		table.remove(voltages_list, 1)
	end    
	
	voltages_list[#voltages_list + 1] = value
	
	for i,voltage in ipairs(voltages_list) do
		sum_voltages = sum_voltages + voltage
	end
	
	collectgarbage()
	return sum_voltages / #voltages_list
end    

local function loop()

	local anCapaGo = system.getInputsVal(anCapaSw)
	local anVoltGo = system.getInputsVal(anVoltSw)
	local tTime = system.getTime()

	--print(collectgarbage("count"))
	
	FlightTime()
	
	gyro_channel = system.getInputs(gyro_output)
		
	txtelemetry = system.getTxTelemetry()
	rx_voltage = txtelemetry.rx1Voltage
	-- rx_percent = txtelemetry.rx1Percent   -- signal quality not used
	rx_a1 = txtelemetry.RSSI[1]
	rx_a2 = txtelemetry.RSSI[2]
		
	-- Read Sensor Parameter 1 Voltage 
	sensor = system.getSensorValueByID(sensorId, 1)
	
	if(sensor and sensor.valid ) then
		battery_voltage = sensor.value
		-- TRY TRY
	--if(sensor) then
	--	battery_voltage = 19
			if (initial_voltage_measured == false) then
				if ( battery_voltage > 3 ) then
					initial_voltage_measured = true
					initial_cell_voltage = battery_voltage / cell_count
					initial_capacity_percent_used = get_capacity_percent_used()
				end    
			end        
			
			-- calculate Min/Max Sensor 1
			if ( battery_voltage < minvtg and battery_voltage > 6 ) then minvtg = battery_voltage end
			if battery_voltage > maxvtg then maxvtg = battery_voltage end
			
			if newTime >= (last_averaging_time + 1000) then          -- one second period, newTime set from FlightTime()
				battery_voltage_average = average(battery_voltage)   -- average voltages over n samples
				last_averaging_time = newTime
			end
			
		else
			battery_voltage = 0
			initial_voltage_measured = false
		end
        
		-- Read Sensor Parameter 2 Current 
		sensor = system.getSensorValueByID(sensorId, 2)
		if(sensor and sensor.valid) then
			motor_current = sensor.value
			-- calculate Min/Max Sensor 2
			if motor_current < mincur then mincur = motor_current end
			if motor_current > maxcur then maxcur = motor_current end
		else
			motor_current = 0
		end

		-- Read Sensor Parameter 3 Rotor RPM
		sensor = system.getSensorValueByID(sensorId, 3)
		if(sensor and sensor.valid) then
			rotor_rpm = sensor.value
			-- calculate Min/Max Sensor 3
			if rotor_rpm < minrpm then minrpm = rotor_rpm end
			if rotor_rpm > maxrpm then maxrpm = rotor_rpm end
		else
			rotor_rpm = 0
		end

		-- Read Sensor Parameter 4 Used Capacity
		sensor = system.getSensorValueByID(sensorId, 4)
		
		if(sensor and sensor.valid and (battery_voltage > 1.0)) then
			used_capacity = sensor.value
		-- TRY TRY
		--if(sensor and (battery_voltage > 1.0)) then
		--	used_capacity = 0
		
			if ( initial_voltage_measured == true ) then
				remaining_capacity_percent = math.floor( ( ( (capacity - used_capacity) * 100) / capacity ) - initial_capacity_percent_used)
				if remaining_capacity_percent < 0 then remaining_capacity_percent = 0 end
			end
            
			if ( remaining_capacity_percent <= capacity_alarm_thresh and capacity_alarm_voice ~= "..." and next_capacity_alarm < tTime ) then
			-- TRY TRY      
			--if(remaining_capacity_percent <= capacity_alarm_thresh and tTime >= next_capacity_alarm ) then    
				system.messageBox(trans.capaWarn,2)
				
				--volume = system.getProperty ("Volume")
			    --volume_playback = system.getProperty ("VolumePlayback")
				--system.setProperty ("Volume", 16)
				--system.setProperty ("VolumePlayback", 100)
				
				system.playFile(capacity_alarm_voice,AUDIO_QUEUE)
				
			    --system.setProperty ("Volume", volume)
			    --system.setProperty ("VolumePlayback", volume_playback) 
				
				next_capacity_alarm = tTime + 4 -- battery percentage alarm every 3 second
			end
        
			if ( battery_voltage_average <= voltage_alarm_dec_thresh and voltage_alarm_voice ~= "..." and next_voltage_alarm < tTime ) then
			-- TRY TRY
			--if ( battery_voltage <= voltage_alarm_dec_thresh and next_voltage_alarm < tTime ) then     
				system.messageBox(trans.voltWarn,2)
			     
				--volume = system.getProperty ("Volume")
			    --volume_playback = system.getProperty ("VolumePlayback")
				--system.setProperty ("Volume", 16)
				--system.setProperty ("VolumePlayback", 100)
			     
				system.playFile(voltage_alarm_voice,AUDIO_QUEUE)
			    
			    --system.setProperty ("Volume", volume)
			    --system.setProperty ("VolumePlayback", volume_playback)
			     
			    next_voltage_alarm = tTime + 4 -- battery voltage alarm every 3 second 
			end    
             
			if(anCapaGo == 1 and tTime >= next_capacity_announcement) then
				system.playNumber(remaining_capacity_percent, 0, "%", "Capacity")
				next_capacity_announcement = tTime + 10 -- say battery percentage every 10 seconds
			end
			
			if(anVoltGo == 1 and tTime >= next_voltage_announcement) then
				system.playNumber(battery_voltage, 1, "V", "U Battery")
				next_voltage_announcement = tTime + 10 -- say battery voltage every 10 seconds
			end
                 
			-- Set max/min percentage to 99/0 for drawing
			if( remaining_capacity_percent > 100 ) then remaining_capacity_percent = 100 end
			if( remaining_capacity_percent < 0 ) then remaining_capacity_percent = 0 end
		end	

		-- Read Sensor Parameter 6 BEC Current
		sensor = system.getSensorValueByID(sensorId, 6)
		if(sensor and sensor.valid) then
			bec_current = sensor.value 
			if bec_current < minrxa then minrxa = bec_current end
			if bec_current > maxrxa then maxrxa = bec_current end
		else
			bec_current = 0
		end

		-- Read Sensor Parameter 8 Governor PWM
		sensor = system.getSensorValueByID(sensorId, 8)
		if(sensor and sensor.valid) then
			pwm_percent = sensor.value
			if pwm_percent < minpwm then minpwm = pwm_percent end
			if pwm_percent > maxpwm then maxpwm = pwm_percent end
		else
			pwm_percent = 0
		end

		-- Read Sensor Parameter 9 FET Temperature
		sensor = system.getSensorValueByID(sensorId, 9)
		if(sensor and sensor.valid) then
			fet_temp = sensor.value 
			if fet_temp < mintmp then mintmp = fet_temp end
			if fet_temp > maxtmp then maxtmp = fet_temp end
		else
			fet_temp = 0
		end
		
	collectgarbage()
	-- print(collectgarbage("count"))   
end
--------------------------------------------------------------------------------
local function init(code1)
	local pLoad, registerForm, registerTelemetry = system.pLoad, system.registerForm, system.registerTelemetry
	model = system.getProperty("Model")
	owner = system.getUserName()
	today = system.getDateTime()
	sensorId = pLoad("sensorId", 0)
	capacity = pLoad("capacity",0)
	cell_count = pLoad("cell_count",0)
	capacity_alarm_thresh = pLoad("capacity_alarm_thresh", 0)
	capacity_alarm_voice = pLoad("capacity_alarm_voice", "...")
	voltage_alarm_thresh = pLoad("voltage_alarm_thresh",0)
	voltage_alarm_dec_thresh = voltage_alarm_thresh / 10             
	voltage_alarm_voice = pLoad("voltage_alarm_voice","...")
	timeSw = pLoad("timeSw")
	resSw = pLoad("resSw")
	anCapaSw = pLoad("anCapaSw")
	anVoltSw = pLoad("anVoltSw")
	gyChannel = pLoad("gyChannel", 1)
	gyro_output = output_list[gyChannel]
	--average = moving_average(5)
	registerForm(1, MENU_APPS, trans.appName, setupForm)
	-- registerTelemetry(1, trans.appName, 4, Page1) --registers a full size Window
	registerTelemetry(1, trans.appName .. "   " .. model, 4, Page1) --registers a full size Window
	collectgarbage()
end
--------------------------------------------------------------------------------
Version = "2.1"
setLanguage()
collectgarbage()
return {init=init, loop=loop, author="Tero Salminen, A. Fromm, Rene S., D. Brueggemann", version=Version, name=trans.appName}
